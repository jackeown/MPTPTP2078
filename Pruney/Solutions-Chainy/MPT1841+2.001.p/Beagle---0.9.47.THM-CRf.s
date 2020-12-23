%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:28 EST 2020

% Result     : Theorem 4.31s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 228 expanded)
%              Number of leaves         :   41 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  132 ( 393 expanded)
%              Number of equality atoms :   38 (  91 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_enumset1 > k6_domain_1 > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_115,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,(
    ! [A_60,B_61] :
      ( l1_pre_topc(g1_pre_topc(A_60,B_61))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_146,plain,(
    ! [A_60] : l1_pre_topc(g1_pre_topc(A_60,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_38,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    ! [B_42,A_43] :
      ( ~ r2_hidden(B_42,A_43)
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [C_9] : ~ v1_xboole_0(k1_tarski(C_9)) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_182,plain,(
    ! [A_68,B_69] :
      ( k6_domain_1(A_68,B_69) = k1_tarski(B_69)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_191,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_182])).

tff(c_196,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_191])).

tff(c_251,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1(k6_domain_1(A_85,B_86),k1_zfmisc_1(A_85))
      | ~ m1_subset_1(B_86,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_270,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_251])).

tff(c_277,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_270])).

tff(c_278,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_277])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_289,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_278,c_24])).

tff(c_50,plain,(
    ! [B_37,A_35] :
      ( B_37 = A_35
      | ~ r1_tarski(A_35,B_37)
      | ~ v1_zfmisc_1(B_37)
      | v1_xboole_0(B_37)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_292,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_289,c_50])).

tff(c_295,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_292])).

tff(c_296,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_295])).

tff(c_54,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_198,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_54])).

tff(c_299,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_198])).

tff(c_171,plain,(
    ! [A_66,B_67] :
      ( v1_pre_topc(g1_pre_topc(A_66,B_67))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_181,plain,(
    ! [A_66] : v1_pre_topc(g1_pre_topc(A_66,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_22,c_171])).

tff(c_147,plain,(
    ! [A_62] : l1_pre_topc(g1_pre_topc(A_62,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_109,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_113,plain,(
    ! [A_23] :
      ( u1_struct_0(A_23) = k2_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_38,c_109])).

tff(c_151,plain,(
    ! [A_62] : u1_struct_0(g1_pre_topc(A_62,k1_xboole_0)) = k2_struct_0(g1_pre_topc(A_62,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_147,c_113])).

tff(c_203,plain,(
    ! [A_71] :
      ( g1_pre_topc(u1_struct_0(A_71),u1_pre_topc(A_71)) = A_71
      | ~ v1_pre_topc(A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_212,plain,(
    ! [A_62] :
      ( g1_pre_topc(k2_struct_0(g1_pre_topc(A_62,k1_xboole_0)),u1_pre_topc(g1_pre_topc(A_62,k1_xboole_0))) = g1_pre_topc(A_62,k1_xboole_0)
      | ~ v1_pre_topc(g1_pre_topc(A_62,k1_xboole_0))
      | ~ l1_pre_topc(g1_pre_topc(A_62,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_203])).

tff(c_842,plain,(
    ! [A_132] : g1_pre_topc(k2_struct_0(g1_pre_topc(A_132,k1_xboole_0)),u1_pre_topc(g1_pre_topc(A_132,k1_xboole_0))) = g1_pre_topc(A_132,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_181,c_212])).

tff(c_42,plain,(
    ! [D_30,B_26,C_29,A_25] :
      ( D_30 = B_26
      | g1_pre_topc(C_29,D_30) != g1_pre_topc(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_847,plain,(
    ! [A_132,B_26,A_25] :
      ( u1_pre_topc(g1_pre_topc(A_132,k1_xboole_0)) = B_26
      | g1_pre_topc(A_25,B_26) != g1_pre_topc(A_132,k1_xboole_0)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_42])).

tff(c_2133,plain,(
    ! [A_132] :
      ( u1_pre_topc(g1_pre_topc(A_132,k1_xboole_0)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_132))) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_847])).

tff(c_2135,plain,(
    ! [A_132] : u1_pre_topc(g1_pre_topc(A_132,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2133])).

tff(c_216,plain,(
    ! [A_62] : g1_pre_topc(k2_struct_0(g1_pre_topc(A_62,k1_xboole_0)),u1_pre_topc(g1_pre_topc(A_62,k1_xboole_0))) = g1_pre_topc(A_62,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_181,c_212])).

tff(c_2180,plain,(
    ! [A_244] : g1_pre_topc(k2_struct_0(g1_pre_topc(A_244,k1_xboole_0)),k1_xboole_0) = g1_pre_topc(A_244,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2135,c_216])).

tff(c_44,plain,(
    ! [C_29,A_25,D_30,B_26] :
      ( C_29 = A_25
      | g1_pre_topc(C_29,D_30) != g1_pre_topc(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2206,plain,(
    ! [A_244,C_29,D_30] :
      ( k2_struct_0(g1_pre_topc(A_244,k1_xboole_0)) = C_29
      | g1_pre_topc(C_29,D_30) != g1_pre_topc(A_244,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(A_244,k1_xboole_0))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2180,c_44])).

tff(c_2234,plain,(
    ! [A_244,C_29,D_30] :
      ( k2_struct_0(g1_pre_topc(A_244,k1_xboole_0)) = C_29
      | g1_pre_topc(C_29,D_30) != g1_pre_topc(A_244,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2206])).

tff(c_2266,plain,(
    ! [A_244] : k2_struct_0(g1_pre_topc(A_244,k1_xboole_0)) = A_244 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2234])).

tff(c_159,plain,(
    ! [A_65] : u1_struct_0(g1_pre_topc(A_65,k1_xboole_0)) = k2_struct_0(g1_pre_topc(A_65,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_147,c_113])).

tff(c_40,plain,(
    ! [A_24] :
      ( ~ v1_subset_1(k2_struct_0(A_24),u1_struct_0(A_24))
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_165,plain,(
    ! [A_65] :
      ( ~ v1_subset_1(k2_struct_0(g1_pre_topc(A_65,k1_xboole_0)),k2_struct_0(g1_pre_topc(A_65,k1_xboole_0)))
      | ~ l1_struct_0(g1_pre_topc(A_65,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_40])).

tff(c_2393,plain,(
    ! [A_257] :
      ( ~ v1_subset_1(A_257,A_257)
      | ~ l1_struct_0(g1_pre_topc(A_257,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2266,c_2266,c_165])).

tff(c_2396,plain,(
    ~ l1_struct_0(g1_pre_topc('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_299,c_2393])).

tff(c_2432,plain,(
    ~ l1_pre_topc(g1_pre_topc('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_38,c_2396])).

tff(c_2436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:18:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.31/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.31/1.83  
% 4.31/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.83  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_enumset1 > k6_domain_1 > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 4.53/1.83  
% 4.53/1.83  %Foreground sorts:
% 4.53/1.83  
% 4.53/1.83  
% 4.53/1.83  %Background operators:
% 4.53/1.83  
% 4.53/1.83  
% 4.53/1.83  %Foreground operators:
% 4.53/1.83  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.53/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.83  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.53/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.83  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.53/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.53/1.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.53/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.53/1.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.53/1.83  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.53/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.53/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.53/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.53/1.83  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.53/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.53/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.53/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.53/1.83  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.53/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.53/1.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.53/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.53/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.53/1.83  
% 4.53/1.85  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.53/1.85  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 4.53/1.85  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.53/1.85  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.53/1.85  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.53/1.85  tff(f_127, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 4.53/1.85  tff(f_102, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.53/1.85  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.53/1.85  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.53/1.85  tff(f_115, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 4.53/1.85  tff(f_64, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.53/1.85  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.53/1.85  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 4.53/1.85  tff(f_79, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 4.53/1.85  tff(c_22, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.53/1.85  tff(c_136, plain, (![A_60, B_61]: (l1_pre_topc(g1_pre_topc(A_60, B_61)) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.53/1.85  tff(c_146, plain, (![A_60]: (l1_pre_topc(g1_pre_topc(A_60, k1_xboole_0)))), inference(resolution, [status(thm)], [c_22, c_136])).
% 4.53/1.85  tff(c_38, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.53/1.85  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.85  tff(c_62, plain, (![B_42, A_43]: (~r2_hidden(B_42, A_43) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.53/1.85  tff(c_66, plain, (![C_9]: (~v1_xboole_0(k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_8, c_62])).
% 4.53/1.85  tff(c_58, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.53/1.85  tff(c_52, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.53/1.85  tff(c_56, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.53/1.85  tff(c_182, plain, (![A_68, B_69]: (k6_domain_1(A_68, B_69)=k1_tarski(B_69) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.53/1.85  tff(c_191, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_182])).
% 4.53/1.85  tff(c_196, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_191])).
% 4.53/1.85  tff(c_251, plain, (![A_85, B_86]: (m1_subset_1(k6_domain_1(A_85, B_86), k1_zfmisc_1(A_85)) | ~m1_subset_1(B_86, A_85) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.53/1.85  tff(c_270, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_196, c_251])).
% 4.53/1.85  tff(c_277, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_270])).
% 4.53/1.85  tff(c_278, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_277])).
% 4.53/1.85  tff(c_24, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.53/1.85  tff(c_289, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_278, c_24])).
% 4.53/1.85  tff(c_50, plain, (![B_37, A_35]: (B_37=A_35 | ~r1_tarski(A_35, B_37) | ~v1_zfmisc_1(B_37) | v1_xboole_0(B_37) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.53/1.85  tff(c_292, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_289, c_50])).
% 4.53/1.85  tff(c_295, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_292])).
% 4.53/1.85  tff(c_296, plain, (k1_tarski('#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_295])).
% 4.53/1.85  tff(c_54, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.53/1.85  tff(c_198, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_54])).
% 4.53/1.85  tff(c_299, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_198])).
% 4.53/1.85  tff(c_171, plain, (![A_66, B_67]: (v1_pre_topc(g1_pre_topc(A_66, B_67)) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.53/1.85  tff(c_181, plain, (![A_66]: (v1_pre_topc(g1_pre_topc(A_66, k1_xboole_0)))), inference(resolution, [status(thm)], [c_22, c_171])).
% 4.53/1.85  tff(c_147, plain, (![A_62]: (l1_pre_topc(g1_pre_topc(A_62, k1_xboole_0)))), inference(resolution, [status(thm)], [c_22, c_136])).
% 4.53/1.85  tff(c_109, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.53/1.85  tff(c_113, plain, (![A_23]: (u1_struct_0(A_23)=k2_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(resolution, [status(thm)], [c_38, c_109])).
% 4.53/1.85  tff(c_151, plain, (![A_62]: (u1_struct_0(g1_pre_topc(A_62, k1_xboole_0))=k2_struct_0(g1_pre_topc(A_62, k1_xboole_0)))), inference(resolution, [status(thm)], [c_147, c_113])).
% 4.53/1.85  tff(c_203, plain, (![A_71]: (g1_pre_topc(u1_struct_0(A_71), u1_pre_topc(A_71))=A_71 | ~v1_pre_topc(A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.53/1.85  tff(c_212, plain, (![A_62]: (g1_pre_topc(k2_struct_0(g1_pre_topc(A_62, k1_xboole_0)), u1_pre_topc(g1_pre_topc(A_62, k1_xboole_0)))=g1_pre_topc(A_62, k1_xboole_0) | ~v1_pre_topc(g1_pre_topc(A_62, k1_xboole_0)) | ~l1_pre_topc(g1_pre_topc(A_62, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_203])).
% 4.53/1.85  tff(c_842, plain, (![A_132]: (g1_pre_topc(k2_struct_0(g1_pre_topc(A_132, k1_xboole_0)), u1_pre_topc(g1_pre_topc(A_132, k1_xboole_0)))=g1_pre_topc(A_132, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_181, c_212])).
% 4.53/1.85  tff(c_42, plain, (![D_30, B_26, C_29, A_25]: (D_30=B_26 | g1_pre_topc(C_29, D_30)!=g1_pre_topc(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_25))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.53/1.85  tff(c_847, plain, (![A_132, B_26, A_25]: (u1_pre_topc(g1_pre_topc(A_132, k1_xboole_0))=B_26 | g1_pre_topc(A_25, B_26)!=g1_pre_topc(A_132, k1_xboole_0) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_25))))), inference(superposition, [status(thm), theory('equality')], [c_842, c_42])).
% 4.53/1.85  tff(c_2133, plain, (![A_132]: (u1_pre_topc(g1_pre_topc(A_132, k1_xboole_0))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_132))))), inference(reflexivity, [status(thm), theory('equality')], [c_847])).
% 4.53/1.85  tff(c_2135, plain, (![A_132]: (u1_pre_topc(g1_pre_topc(A_132, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2133])).
% 4.53/1.85  tff(c_216, plain, (![A_62]: (g1_pre_topc(k2_struct_0(g1_pre_topc(A_62, k1_xboole_0)), u1_pre_topc(g1_pre_topc(A_62, k1_xboole_0)))=g1_pre_topc(A_62, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_181, c_212])).
% 4.53/1.85  tff(c_2180, plain, (![A_244]: (g1_pre_topc(k2_struct_0(g1_pre_topc(A_244, k1_xboole_0)), k1_xboole_0)=g1_pre_topc(A_244, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2135, c_216])).
% 4.53/1.85  tff(c_44, plain, (![C_29, A_25, D_30, B_26]: (C_29=A_25 | g1_pre_topc(C_29, D_30)!=g1_pre_topc(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_25))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.53/1.85  tff(c_2206, plain, (![A_244, C_29, D_30]: (k2_struct_0(g1_pre_topc(A_244, k1_xboole_0))=C_29 | g1_pre_topc(C_29, D_30)!=g1_pre_topc(A_244, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(A_244, k1_xboole_0))))))), inference(superposition, [status(thm), theory('equality')], [c_2180, c_44])).
% 4.53/1.85  tff(c_2234, plain, (![A_244, C_29, D_30]: (k2_struct_0(g1_pre_topc(A_244, k1_xboole_0))=C_29 | g1_pre_topc(C_29, D_30)!=g1_pre_topc(A_244, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2206])).
% 4.53/1.85  tff(c_2266, plain, (![A_244]: (k2_struct_0(g1_pre_topc(A_244, k1_xboole_0))=A_244)), inference(reflexivity, [status(thm), theory('equality')], [c_2234])).
% 4.53/1.85  tff(c_159, plain, (![A_65]: (u1_struct_0(g1_pre_topc(A_65, k1_xboole_0))=k2_struct_0(g1_pre_topc(A_65, k1_xboole_0)))), inference(resolution, [status(thm)], [c_147, c_113])).
% 4.53/1.85  tff(c_40, plain, (![A_24]: (~v1_subset_1(k2_struct_0(A_24), u1_struct_0(A_24)) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.53/1.85  tff(c_165, plain, (![A_65]: (~v1_subset_1(k2_struct_0(g1_pre_topc(A_65, k1_xboole_0)), k2_struct_0(g1_pre_topc(A_65, k1_xboole_0))) | ~l1_struct_0(g1_pre_topc(A_65, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_40])).
% 4.53/1.85  tff(c_2393, plain, (![A_257]: (~v1_subset_1(A_257, A_257) | ~l1_struct_0(g1_pre_topc(A_257, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2266, c_2266, c_165])).
% 4.53/1.85  tff(c_2396, plain, (~l1_struct_0(g1_pre_topc('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_299, c_2393])).
% 4.53/1.85  tff(c_2432, plain, (~l1_pre_topc(g1_pre_topc('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_2396])).
% 4.53/1.85  tff(c_2436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_2432])).
% 4.53/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.85  
% 4.53/1.85  Inference rules
% 4.53/1.85  ----------------------
% 4.53/1.85  #Ref     : 10
% 4.53/1.85  #Sup     : 534
% 4.53/1.85  #Fact    : 0
% 4.53/1.85  #Define  : 0
% 4.53/1.85  #Split   : 7
% 4.53/1.85  #Chain   : 0
% 4.53/1.85  #Close   : 0
% 4.53/1.85  
% 4.53/1.85  Ordering : KBO
% 4.53/1.85  
% 4.53/1.85  Simplification rules
% 4.53/1.85  ----------------------
% 4.53/1.85  #Subsume      : 95
% 4.53/1.85  #Demod        : 206
% 4.53/1.85  #Tautology    : 190
% 4.53/1.85  #SimpNegUnit  : 71
% 4.53/1.85  #BackRed      : 10
% 4.53/1.85  
% 4.53/1.85  #Partial instantiations: 0
% 4.53/1.85  #Strategies tried      : 1
% 4.53/1.85  
% 4.53/1.85  Timing (in seconds)
% 4.53/1.85  ----------------------
% 4.53/1.85  Preprocessing        : 0.33
% 4.53/1.85  Parsing              : 0.17
% 4.53/1.85  CNF conversion       : 0.02
% 4.53/1.85  Main loop            : 0.72
% 4.53/1.85  Inferencing          : 0.25
% 4.53/1.85  Reduction            : 0.21
% 4.53/1.85  Demodulation         : 0.14
% 4.53/1.85  BG Simplification    : 0.03
% 4.53/1.85  Subsumption          : 0.16
% 4.53/1.85  Abstraction          : 0.04
% 4.53/1.85  MUC search           : 0.00
% 4.53/1.85  Cooper               : 0.00
% 4.62/1.85  Total                : 1.08
% 4.62/1.85  Index Insertion      : 0.00
% 4.62/1.85  Index Deletion       : 0.00
% 4.62/1.85  Index Matching       : 0.00
% 4.62/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
