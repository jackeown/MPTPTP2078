%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:48 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 158 expanded)
%              Number of leaves         :   46 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  121 ( 260 expanded)
%              Number of equality atoms :   39 (  58 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_90,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_38,plain,(
    ! [A_25] : l1_orders_2(k2_yellow_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_14] : v1_xboole_0('#skF_1'(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    ! [A_14] : '#skF_1'(A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_56])).

tff(c_20,plain,(
    ! [A_14] : m1_subset_1('#skF_1'(A_14),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_20])).

tff(c_125,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_129,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_102,c_125])).

tff(c_150,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_154,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_150])).

tff(c_185,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_185])).

tff(c_198,plain,(
    ! [A_63] : k4_xboole_0(k1_xboole_0,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_194])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_203,plain,(
    ! [A_63] : k5_xboole_0(A_63,k1_xboole_0) = k2_xboole_0(A_63,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_10])).

tff(c_209,plain,(
    ! [A_64] : k2_xboole_0(A_64,k1_xboole_0) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_203])).

tff(c_16,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),B_13) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_216,plain,(
    ! [A_12] : k1_tarski(A_12) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_16])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_50,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_223,plain,(
    ! [A_66,B_67] :
      ( k6_domain_1(A_66,B_67) = k1_tarski(B_67)
      | ~ m1_subset_1(B_67,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_232,plain,
    ( k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_223])).

tff(c_237,plain,(
    k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_232])).

tff(c_254,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k6_domain_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_263,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_254])).

tff(c_267,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_263])).

tff(c_268,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_267])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_276,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_268,c_22])).

tff(c_44,plain,(
    ! [B_29,A_27] :
      ( B_29 = A_27
      | ~ r1_tarski(A_27,B_29)
      | ~ v1_zfmisc_1(B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_279,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_276,c_44])).

tff(c_285,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_279])).

tff(c_286,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_285])).

tff(c_288,plain,(
    v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_291,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_288,c_2])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_291])).

tff(c_296,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_48,plain,(
    v1_subset_1(k6_domain_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_244,plain,(
    v1_subset_1(k1_tarski('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_48])).

tff(c_300,plain,(
    v1_subset_1('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_244])).

tff(c_40,plain,(
    ! [A_26] : u1_struct_0(k2_yellow_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_114,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_119,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_orders_2(A_45) ) ),
    inference(resolution,[status(thm)],[c_32,c_114])).

tff(c_122,plain,(
    ! [A_25] : u1_struct_0(k2_yellow_1(A_25)) = k2_struct_0(k2_yellow_1(A_25)) ),
    inference(resolution,[status(thm)],[c_38,c_119])).

tff(c_124,plain,(
    ! [A_25] : k2_struct_0(k2_yellow_1(A_25)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_122])).

tff(c_140,plain,(
    ! [A_50] :
      ( ~ v1_subset_1(k2_struct_0(A_50),u1_struct_0(A_50))
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_146,plain,(
    ! [A_26] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_26)),A_26)
      | ~ l1_struct_0(k2_yellow_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_140])).

tff(c_148,plain,(
    ! [A_26] :
      ( ~ v1_subset_1(A_26,A_26)
      | ~ l1_struct_0(k2_yellow_1(A_26)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_146])).

tff(c_322,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_300,c_148])).

tff(c_345,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_322])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:16:31 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.31  
% 2.48/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.31  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.48/1.31  
% 2.48/1.31  %Foreground sorts:
% 2.48/1.31  
% 2.48/1.31  
% 2.48/1.31  %Background operators:
% 2.48/1.31  
% 2.48/1.31  
% 2.48/1.31  %Foreground operators:
% 2.48/1.31  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.48/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.31  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.48/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.48/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.31  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.48/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.48/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.48/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.48/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.48/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.31  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.48/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.31  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.48/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.31  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.48/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.48/1.31  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.48/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.48/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.31  
% 2.48/1.33  tff(f_86, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.48/1.33  tff(f_75, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.48/1.33  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.48/1.33  tff(f_51, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.48/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.48/1.33  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.48/1.33  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.48/1.33  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.48/1.33  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.48/1.33  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.48/1.33  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.48/1.33  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.48/1.33  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.48/1.33  tff(f_103, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.48/1.33  tff(f_90, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.48/1.33  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.48/1.33  tff(f_64, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.48/1.33  tff(c_38, plain, (![A_25]: (l1_orders_2(k2_yellow_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.48/1.33  tff(c_32, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.33  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.33  tff(c_18, plain, (![A_14]: (v1_xboole_0('#skF_1'(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.48/1.33  tff(c_56, plain, (![A_34]: (k1_xboole_0=A_34 | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.33  tff(c_60, plain, (![A_14]: ('#skF_1'(A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_56])).
% 2.48/1.33  tff(c_20, plain, (![A_14]: (m1_subset_1('#skF_1'(A_14), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.48/1.33  tff(c_102, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_20])).
% 2.48/1.33  tff(c_125, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.33  tff(c_129, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_102, c_125])).
% 2.48/1.33  tff(c_150, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.33  tff(c_154, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_129, c_150])).
% 2.48/1.33  tff(c_185, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.33  tff(c_194, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_14))), inference(superposition, [status(thm), theory('equality')], [c_154, c_185])).
% 2.48/1.33  tff(c_198, plain, (![A_63]: (k4_xboole_0(k1_xboole_0, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_194])).
% 2.48/1.33  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.48/1.33  tff(c_203, plain, (![A_63]: (k5_xboole_0(A_63, k1_xboole_0)=k2_xboole_0(A_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_198, c_10])).
% 2.48/1.33  tff(c_209, plain, (![A_64]: (k2_xboole_0(A_64, k1_xboole_0)=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_203])).
% 2.48/1.33  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.48/1.33  tff(c_216, plain, (![A_12]: (k1_tarski(A_12)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_16])).
% 2.48/1.33  tff(c_52, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.48/1.33  tff(c_46, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.48/1.33  tff(c_50, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.48/1.33  tff(c_223, plain, (![A_66, B_67]: (k6_domain_1(A_66, B_67)=k1_tarski(B_67) | ~m1_subset_1(B_67, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.48/1.33  tff(c_232, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_223])).
% 2.48/1.33  tff(c_237, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_232])).
% 2.48/1.33  tff(c_254, plain, (![A_71, B_72]: (m1_subset_1(k6_domain_1(A_71, B_72), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.33  tff(c_263, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_237, c_254])).
% 2.48/1.33  tff(c_267, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_263])).
% 2.48/1.33  tff(c_268, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_267])).
% 2.48/1.33  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.33  tff(c_276, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_268, c_22])).
% 2.48/1.33  tff(c_44, plain, (![B_29, A_27]: (B_29=A_27 | ~r1_tarski(A_27, B_29) | ~v1_zfmisc_1(B_29) | v1_xboole_0(B_29) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.48/1.33  tff(c_279, plain, (k1_tarski('#skF_3')='#skF_2' | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2') | v1_xboole_0(k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_276, c_44])).
% 2.48/1.33  tff(c_285, plain, (k1_tarski('#skF_3')='#skF_2' | v1_xboole_0('#skF_2') | v1_xboole_0(k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_279])).
% 2.48/1.33  tff(c_286, plain, (k1_tarski('#skF_3')='#skF_2' | v1_xboole_0(k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_285])).
% 2.48/1.33  tff(c_288, plain, (v1_xboole_0(k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_286])).
% 2.48/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.33  tff(c_291, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_288, c_2])).
% 2.48/1.33  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_291])).
% 2.48/1.33  tff(c_296, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_286])).
% 2.48/1.33  tff(c_48, plain, (v1_subset_1(k6_domain_1('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.48/1.33  tff(c_244, plain, (v1_subset_1(k1_tarski('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_48])).
% 2.48/1.33  tff(c_300, plain, (v1_subset_1('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_244])).
% 2.48/1.33  tff(c_40, plain, (![A_26]: (u1_struct_0(k2_yellow_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.48/1.33  tff(c_114, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.48/1.33  tff(c_119, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_orders_2(A_45))), inference(resolution, [status(thm)], [c_32, c_114])).
% 2.48/1.33  tff(c_122, plain, (![A_25]: (u1_struct_0(k2_yellow_1(A_25))=k2_struct_0(k2_yellow_1(A_25)))), inference(resolution, [status(thm)], [c_38, c_119])).
% 2.48/1.33  tff(c_124, plain, (![A_25]: (k2_struct_0(k2_yellow_1(A_25))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_122])).
% 2.48/1.33  tff(c_140, plain, (![A_50]: (~v1_subset_1(k2_struct_0(A_50), u1_struct_0(A_50)) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.48/1.33  tff(c_146, plain, (![A_26]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_26)), A_26) | ~l1_struct_0(k2_yellow_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_140])).
% 2.48/1.33  tff(c_148, plain, (![A_26]: (~v1_subset_1(A_26, A_26) | ~l1_struct_0(k2_yellow_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_146])).
% 2.48/1.33  tff(c_322, plain, (~l1_struct_0(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_300, c_148])).
% 2.48/1.33  tff(c_345, plain, (~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_322])).
% 2.48/1.33  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_345])).
% 2.48/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.33  
% 2.48/1.33  Inference rules
% 2.48/1.33  ----------------------
% 2.48/1.33  #Ref     : 0
% 2.48/1.33  #Sup     : 63
% 2.48/1.33  #Fact    : 0
% 2.48/1.33  #Define  : 0
% 2.48/1.33  #Split   : 1
% 2.48/1.33  #Chain   : 0
% 2.48/1.33  #Close   : 0
% 2.48/1.33  
% 2.48/1.33  Ordering : KBO
% 2.48/1.33  
% 2.48/1.33  Simplification rules
% 2.48/1.33  ----------------------
% 2.48/1.33  #Subsume      : 2
% 2.48/1.33  #Demod        : 18
% 2.48/1.33  #Tautology    : 32
% 2.48/1.33  #SimpNegUnit  : 5
% 2.48/1.33  #BackRed      : 6
% 2.48/1.33  
% 2.48/1.33  #Partial instantiations: 0
% 2.48/1.33  #Strategies tried      : 1
% 2.48/1.33  
% 2.48/1.33  Timing (in seconds)
% 2.48/1.33  ----------------------
% 2.48/1.33  Preprocessing        : 0.32
% 2.48/1.33  Parsing              : 0.17
% 2.48/1.33  CNF conversion       : 0.02
% 2.48/1.33  Main loop            : 0.22
% 2.48/1.33  Inferencing          : 0.09
% 2.48/1.33  Reduction            : 0.07
% 2.48/1.33  Demodulation         : 0.05
% 2.48/1.33  BG Simplification    : 0.01
% 2.48/1.33  Subsumption          : 0.02
% 2.48/1.33  Abstraction          : 0.01
% 2.48/1.33  MUC search           : 0.00
% 2.48/1.33  Cooper               : 0.00
% 2.48/1.33  Total                : 0.58
% 2.48/1.33  Index Insertion      : 0.00
% 2.48/1.33  Index Deletion       : 0.00
% 2.48/1.33  Index Matching       : 0.00
% 2.48/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
