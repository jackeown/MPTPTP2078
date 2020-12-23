%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:33 EST 2020

% Result     : Theorem 11.78s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 145 expanded)
%              Number of leaves         :   34 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  111 ( 290 expanded)
%              Number of equality atoms :   25 (  59 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_tops_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_52,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_56])).

tff(c_18,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    ! [A_17] : m1_subset_1('#skF_6',k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_18])).

tff(c_309,plain,(
    ! [A_107,B_108] :
      ( r1_tarski('#skF_4'(A_107,B_108),B_108)
      | v2_tex_2(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_419,plain,(
    ! [A_120] :
      ( r1_tarski('#skF_4'(A_120,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_62,c_309])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_75,plain,(
    ! [A_7] :
      ( A_7 = '#skF_6'
      | ~ r1_tarski(A_7,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_10])).

tff(c_430,plain,(
    ! [A_121] :
      ( '#skF_4'(A_121,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_419,c_75])).

tff(c_44,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_433,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_430,c_44])).

tff(c_436,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_433])).

tff(c_28,plain,(
    ! [A_23] :
      ( v3_pre_topc('#skF_2'(A_23),A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [A_23] :
      ( m1_subset_1('#skF_2'(A_23),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_136,plain,(
    ! [A_78,B_79,C_80] :
      ( k9_subset_1(A_78,B_79,C_80) = k3_xboole_0(B_79,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_145,plain,(
    ! [A_17,B_79] : k9_subset_1(A_17,B_79,'#skF_6') = k3_xboole_0(B_79,'#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_136])).

tff(c_170,plain,(
    ! [A_89,B_90,C_91] :
      ( m1_subset_1(k9_subset_1(A_89,B_90,C_91),k1_zfmisc_1(A_89))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_180,plain,(
    ! [B_79,A_17] :
      ( m1_subset_1(k3_xboole_0(B_79,'#skF_6'),k1_zfmisc_1(A_17))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_170])).

tff(c_186,plain,(
    ! [B_92,A_93] : m1_subset_1(k3_xboole_0(B_92,'#skF_6'),k1_zfmisc_1(A_93)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_180])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_197,plain,(
    ! [B_94,A_95] : r1_tarski(k3_xboole_0(B_94,'#skF_6'),A_95) ),
    inference(resolution,[status(thm)],[c_186,c_20])).

tff(c_205,plain,(
    ! [B_94] : k3_xboole_0(B_94,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_197,c_75])).

tff(c_208,plain,(
    ! [A_17,B_79] : k9_subset_1(A_17,B_79,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_145])).

tff(c_252,plain,(
    ! [A_101,C_102,B_103] :
      ( k9_subset_1(A_101,C_102,B_103) = k9_subset_1(A_101,B_103,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_260,plain,(
    ! [A_17,B_103] : k9_subset_1(A_17,B_103,'#skF_6') = k9_subset_1(A_17,'#skF_6',B_103) ),
    inference(resolution,[status(thm)],[c_62,c_252])).

tff(c_265,plain,(
    ! [A_17,B_103] : k9_subset_1(A_17,'#skF_6',B_103) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_260])).

tff(c_640,plain,(
    ! [A_136,B_137,D_138] :
      ( k9_subset_1(u1_struct_0(A_136),B_137,D_138) != '#skF_4'(A_136,B_137)
      | ~ v3_pre_topc(D_138,A_136)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(u1_struct_0(A_136)))
      | v2_tex_2(B_137,A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_646,plain,(
    ! [A_136,B_103] :
      ( '#skF_4'(A_136,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc(B_103,A_136)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_136)))
      | v2_tex_2('#skF_6',A_136)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_640])).

tff(c_21630,plain,(
    ! [A_648,B_649] :
      ( '#skF_4'(A_648,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc(B_649,A_648)
      | ~ m1_subset_1(B_649,k1_zfmisc_1(u1_struct_0(A_648)))
      | v2_tex_2('#skF_6',A_648)
      | ~ l1_pre_topc(A_648) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_646])).

tff(c_22068,plain,(
    ! [A_657] :
      ( '#skF_4'(A_657,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_2'(A_657),A_657)
      | v2_tex_2('#skF_6',A_657)
      | ~ l1_pre_topc(A_657)
      | ~ v2_pre_topc(A_657) ) ),
    inference(resolution,[status(thm)],[c_30,c_21630])).

tff(c_22073,plain,(
    ! [A_658] :
      ( '#skF_4'(A_658,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_658)
      | ~ l1_pre_topc(A_658)
      | ~ v2_pre_topc(A_658) ) ),
    inference(resolution,[status(thm)],[c_28,c_22068])).

tff(c_22076,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22073,c_44])).

tff(c_22080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_436,c_22076])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.78/4.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/4.45  
% 11.78/4.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/4.45  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 11.78/4.45  
% 11.78/4.45  %Foreground sorts:
% 11.78/4.45  
% 11.78/4.45  
% 11.78/4.45  %Background operators:
% 11.78/4.45  
% 11.78/4.45  
% 11.78/4.45  %Foreground operators:
% 11.78/4.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.78/4.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.78/4.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.78/4.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.78/4.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.78/4.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.78/4.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.78/4.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.78/4.45  tff('#skF_5', type, '#skF_5': $i).
% 11.78/4.45  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 11.78/4.45  tff('#skF_6', type, '#skF_6': $i).
% 11.78/4.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.78/4.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.78/4.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.78/4.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.78/4.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.78/4.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.78/4.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.78/4.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.78/4.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.78/4.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.78/4.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.78/4.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.78/4.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.78/4.45  
% 11.78/4.46  tff(f_111, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 11.78/4.46  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.78/4.46  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.78/4.46  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 11.78/4.46  tff(f_40, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 11.78/4.46  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_tops_1)).
% 11.78/4.46  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.78/4.46  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 11.78/4.46  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.78/4.46  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 11.78/4.46  tff(c_52, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.78/4.46  tff(c_50, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.78/4.46  tff(c_48, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.78/4.46  tff(c_56, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.78/4.46  tff(c_60, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_48, c_56])).
% 11.78/4.46  tff(c_18, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.78/4.46  tff(c_62, plain, (![A_17]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_18])).
% 11.78/4.46  tff(c_309, plain, (![A_107, B_108]: (r1_tarski('#skF_4'(A_107, B_108), B_108) | v2_tex_2(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.78/4.46  tff(c_419, plain, (![A_120]: (r1_tarski('#skF_4'(A_120, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_120) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_62, c_309])).
% 11.78/4.46  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.78/4.46  tff(c_75, plain, (![A_7]: (A_7='#skF_6' | ~r1_tarski(A_7, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_10])).
% 11.78/4.46  tff(c_430, plain, (![A_121]: ('#skF_4'(A_121, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_121) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_419, c_75])).
% 11.78/4.46  tff(c_44, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.78/4.46  tff(c_433, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_430, c_44])).
% 11.78/4.46  tff(c_436, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_433])).
% 11.78/4.46  tff(c_28, plain, (![A_23]: (v3_pre_topc('#skF_2'(A_23), A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.78/4.46  tff(c_30, plain, (![A_23]: (m1_subset_1('#skF_2'(A_23), k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.78/4.46  tff(c_136, plain, (![A_78, B_79, C_80]: (k9_subset_1(A_78, B_79, C_80)=k3_xboole_0(B_79, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.78/4.46  tff(c_145, plain, (![A_17, B_79]: (k9_subset_1(A_17, B_79, '#skF_6')=k3_xboole_0(B_79, '#skF_6'))), inference(resolution, [status(thm)], [c_62, c_136])).
% 11.78/4.46  tff(c_170, plain, (![A_89, B_90, C_91]: (m1_subset_1(k9_subset_1(A_89, B_90, C_91), k1_zfmisc_1(A_89)) | ~m1_subset_1(C_91, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.78/4.46  tff(c_180, plain, (![B_79, A_17]: (m1_subset_1(k3_xboole_0(B_79, '#skF_6'), k1_zfmisc_1(A_17)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_170])).
% 11.78/4.46  tff(c_186, plain, (![B_92, A_93]: (m1_subset_1(k3_xboole_0(B_92, '#skF_6'), k1_zfmisc_1(A_93)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_180])).
% 11.78/4.46  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.78/4.46  tff(c_197, plain, (![B_94, A_95]: (r1_tarski(k3_xboole_0(B_94, '#skF_6'), A_95))), inference(resolution, [status(thm)], [c_186, c_20])).
% 11.78/4.46  tff(c_205, plain, (![B_94]: (k3_xboole_0(B_94, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_197, c_75])).
% 11.78/4.46  tff(c_208, plain, (![A_17, B_79]: (k9_subset_1(A_17, B_79, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_145])).
% 11.78/4.46  tff(c_252, plain, (![A_101, C_102, B_103]: (k9_subset_1(A_101, C_102, B_103)=k9_subset_1(A_101, B_103, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.78/4.46  tff(c_260, plain, (![A_17, B_103]: (k9_subset_1(A_17, B_103, '#skF_6')=k9_subset_1(A_17, '#skF_6', B_103))), inference(resolution, [status(thm)], [c_62, c_252])).
% 11.78/4.46  tff(c_265, plain, (![A_17, B_103]: (k9_subset_1(A_17, '#skF_6', B_103)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_260])).
% 11.78/4.46  tff(c_640, plain, (![A_136, B_137, D_138]: (k9_subset_1(u1_struct_0(A_136), B_137, D_138)!='#skF_4'(A_136, B_137) | ~v3_pre_topc(D_138, A_136) | ~m1_subset_1(D_138, k1_zfmisc_1(u1_struct_0(A_136))) | v2_tex_2(B_137, A_136) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.78/4.46  tff(c_646, plain, (![A_136, B_103]: ('#skF_4'(A_136, '#skF_6')!='#skF_6' | ~v3_pre_topc(B_103, A_136) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_136))) | v2_tex_2('#skF_6', A_136) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(superposition, [status(thm), theory('equality')], [c_265, c_640])).
% 11.78/4.46  tff(c_21630, plain, (![A_648, B_649]: ('#skF_4'(A_648, '#skF_6')!='#skF_6' | ~v3_pre_topc(B_649, A_648) | ~m1_subset_1(B_649, k1_zfmisc_1(u1_struct_0(A_648))) | v2_tex_2('#skF_6', A_648) | ~l1_pre_topc(A_648))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_646])).
% 11.78/4.46  tff(c_22068, plain, (![A_657]: ('#skF_4'(A_657, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_2'(A_657), A_657) | v2_tex_2('#skF_6', A_657) | ~l1_pre_topc(A_657) | ~v2_pre_topc(A_657))), inference(resolution, [status(thm)], [c_30, c_21630])).
% 11.78/4.46  tff(c_22073, plain, (![A_658]: ('#skF_4'(A_658, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_658) | ~l1_pre_topc(A_658) | ~v2_pre_topc(A_658))), inference(resolution, [status(thm)], [c_28, c_22068])).
% 11.78/4.46  tff(c_22076, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22073, c_44])).
% 11.78/4.46  tff(c_22080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_436, c_22076])).
% 11.78/4.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/4.46  
% 11.78/4.46  Inference rules
% 11.78/4.46  ----------------------
% 11.78/4.46  #Ref     : 0
% 11.78/4.46  #Sup     : 5433
% 11.78/4.46  #Fact    : 0
% 11.78/4.46  #Define  : 0
% 11.78/4.46  #Split   : 9
% 11.78/4.46  #Chain   : 0
% 11.78/4.46  #Close   : 0
% 11.78/4.46  
% 11.78/4.46  Ordering : KBO
% 11.78/4.46  
% 11.78/4.46  Simplification rules
% 11.78/4.46  ----------------------
% 11.78/4.46  #Subsume      : 702
% 11.78/4.46  #Demod        : 4901
% 11.78/4.46  #Tautology    : 1930
% 11.78/4.46  #SimpNegUnit  : 32
% 11.78/4.46  #BackRed      : 11
% 11.78/4.46  
% 11.78/4.46  #Partial instantiations: 0
% 11.78/4.46  #Strategies tried      : 1
% 11.78/4.46  
% 11.78/4.46  Timing (in seconds)
% 11.78/4.46  ----------------------
% 11.78/4.47  Preprocessing        : 0.32
% 11.78/4.47  Parsing              : 0.16
% 11.78/4.47  CNF conversion       : 0.02
% 11.78/4.47  Main loop            : 3.35
% 11.78/4.47  Inferencing          : 0.92
% 11.78/4.47  Reduction            : 1.10
% 11.78/4.47  Demodulation         : 0.85
% 11.78/4.47  BG Simplification    : 0.12
% 11.78/4.47  Subsumption          : 0.97
% 11.78/4.47  Abstraction          : 0.17
% 11.78/4.47  MUC search           : 0.00
% 11.78/4.47  Cooper               : 0.00
% 11.78/4.47  Total                : 3.69
% 11.78/4.47  Index Insertion      : 0.00
% 11.78/4.47  Index Deletion       : 0.00
% 11.78/4.47  Index Matching       : 0.00
% 11.78/4.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
