%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:24 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 232 expanded)
%              Number of leaves         :   34 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  134 ( 529 expanded)
%              Number of equality atoms :   27 ( 106 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_mcart_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_116,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_52,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_56,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_67,plain,(
    ! [A_68] :
      ( k1_xboole_0 = A_68
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_76,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_67])).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [A_13] : m1_subset_1('#skF_6',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_22])).

tff(c_96,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_104,plain,(
    ! [A_13] : r1_tarski('#skF_6',A_13) ),
    inference(resolution,[status(thm)],[c_78,c_96])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = '#skF_6'
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14])).

tff(c_123,plain,(
    ! [A_13] : k4_xboole_0('#skF_6',A_13) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_104,c_109])).

tff(c_546,plain,(
    ! [A_141,B_142] :
      ( r1_tarski('#skF_4'(A_141,B_142),B_142)
      | v2_tex_2(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_705,plain,(
    ! [A_156] :
      ( r1_tarski('#skF_4'(A_156,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_78,c_546])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_198,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12])).

tff(c_209,plain,(
    ! [B_89,A_90] :
      ( B_89 = A_90
      | ~ r1_tarski(B_89,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_220,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | k4_xboole_0(A_4,B_5) != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_198,c_209])).

tff(c_708,plain,(
    ! [A_156] :
      ( '#skF_4'(A_156,'#skF_6') = '#skF_6'
      | k4_xboole_0('#skF_6','#skF_4'(A_156,'#skF_6')) != '#skF_6'
      | v2_tex_2('#skF_6',A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_705,c_220])).

tff(c_731,plain,(
    ! [A_157] :
      ( '#skF_4'(A_157,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_157)
      | ~ l1_pre_topc(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_708])).

tff(c_734,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_731,c_52])).

tff(c_737,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_734])).

tff(c_60,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_637,plain,(
    ! [A_149,B_150] :
      ( m1_subset_1('#skF_4'(A_149,B_150),k1_zfmisc_1(u1_struct_0(A_149)))
      | v2_tex_2(B_150,A_149)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    ! [B_38,A_36] :
      ( v3_pre_topc(B_38,A_36)
      | ~ v1_xboole_0(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2229,plain,(
    ! [A_244,B_245] :
      ( v3_pre_topc('#skF_4'(A_244,B_245),A_244)
      | ~ v1_xboole_0('#skF_4'(A_244,B_245))
      | ~ v2_pre_topc(A_244)
      | v2_tex_2(B_245,A_244)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ l1_pre_topc(A_244) ) ),
    inference(resolution,[status(thm)],[c_637,c_38])).

tff(c_2907,plain,(
    ! [A_288] :
      ( v3_pre_topc('#skF_4'(A_288,'#skF_6'),A_288)
      | ~ v1_xboole_0('#skF_4'(A_288,'#skF_6'))
      | ~ v2_pre_topc(A_288)
      | v2_tex_2('#skF_6',A_288)
      | ~ l1_pre_topc(A_288) ) ),
    inference(resolution,[status(thm)],[c_78,c_2229])).

tff(c_2910,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_5')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_737,c_2907])).

tff(c_2912,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_56,c_737,c_2910])).

tff(c_2913,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2912])).

tff(c_18,plain,(
    ! [A_8] : m1_subset_1('#skF_1'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_273,plain,(
    ! [A_92,B_93,C_94] :
      ( k9_subset_1(A_92,B_93,B_93) = B_93
      | ~ m1_subset_1(C_94,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_282,plain,(
    ! [A_92,B_93] : k9_subset_1(A_92,B_93,B_93) = B_93 ),
    inference(resolution,[status(thm)],[c_18,c_273])).

tff(c_874,plain,(
    ! [A_168,B_169,D_170] :
      ( k9_subset_1(u1_struct_0(A_168),B_169,D_170) != '#skF_4'(A_168,B_169)
      | ~ v3_pre_topc(D_170,A_168)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(u1_struct_0(A_168)))
      | v2_tex_2(B_169,A_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7166,plain,(
    ! [A_496,B_497] :
      ( '#skF_4'(A_496,B_497) != B_497
      | ~ v3_pre_topc(B_497,A_496)
      | ~ m1_subset_1(B_497,k1_zfmisc_1(u1_struct_0(A_496)))
      | v2_tex_2(B_497,A_496)
      | ~ m1_subset_1(B_497,k1_zfmisc_1(u1_struct_0(A_496)))
      | ~ l1_pre_topc(A_496) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_874])).

tff(c_7194,plain,(
    ! [A_496] :
      ( '#skF_4'(A_496,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_496)
      | v2_tex_2('#skF_6',A_496)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_496)))
      | ~ l1_pre_topc(A_496) ) ),
    inference(resolution,[status(thm)],[c_78,c_7166])).

tff(c_7213,plain,(
    ! [A_498] :
      ( '#skF_4'(A_498,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_498)
      | v2_tex_2('#skF_6',A_498)
      | ~ l1_pre_topc(A_498) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7194])).

tff(c_7216,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2913,c_7213])).

tff(c_7222,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_737,c_7216])).

tff(c_7224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:54:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.80/2.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.80  
% 7.80/2.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.80  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_mcart_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 7.80/2.80  
% 7.80/2.80  %Foreground sorts:
% 7.80/2.80  
% 7.80/2.80  
% 7.80/2.80  %Background operators:
% 7.80/2.80  
% 7.80/2.80  
% 7.80/2.80  %Foreground operators:
% 7.80/2.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.80/2.80  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.80/2.80  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.80/2.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.80/2.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.80/2.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.80/2.80  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.80/2.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.80/2.80  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.80/2.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.80/2.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.80/2.80  tff('#skF_5', type, '#skF_5': $i).
% 7.80/2.80  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.80/2.80  tff('#skF_6', type, '#skF_6': $i).
% 7.80/2.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.80/2.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.80/2.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.80/2.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.80/2.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.80/2.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.80/2.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.80/2.80  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.80/2.80  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.80/2.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.80/2.80  
% 7.80/2.82  tff(f_131, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 7.80/2.82  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.80/2.82  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.80/2.82  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.80/2.82  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.80/2.82  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 7.80/2.82  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.80/2.82  tff(f_95, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 7.80/2.82  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 7.80/2.82  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 7.80/2.82  tff(c_52, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.80/2.82  tff(c_58, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.80/2.82  tff(c_56, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.80/2.82  tff(c_67, plain, (![A_68]: (k1_xboole_0=A_68 | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.80/2.82  tff(c_76, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_56, c_67])).
% 7.80/2.82  tff(c_22, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.80/2.82  tff(c_78, plain, (![A_13]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_22])).
% 7.80/2.82  tff(c_96, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | ~m1_subset_1(A_74, k1_zfmisc_1(B_75)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.80/2.82  tff(c_104, plain, (![A_13]: (r1_tarski('#skF_6', A_13))), inference(resolution, [status(thm)], [c_78, c_96])).
% 7.80/2.82  tff(c_14, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k1_xboole_0 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.80/2.82  tff(c_109, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)='#skF_6' | ~r1_tarski(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_14])).
% 7.80/2.82  tff(c_123, plain, (![A_13]: (k4_xboole_0('#skF_6', A_13)='#skF_6')), inference(resolution, [status(thm)], [c_104, c_109])).
% 7.80/2.82  tff(c_546, plain, (![A_141, B_142]: (r1_tarski('#skF_4'(A_141, B_142), B_142) | v2_tex_2(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.80/2.82  tff(c_705, plain, (![A_156]: (r1_tarski('#skF_4'(A_156, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_156) | ~l1_pre_topc(A_156))), inference(resolution, [status(thm)], [c_78, c_546])).
% 7.80/2.82  tff(c_12, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.80/2.82  tff(c_198, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12])).
% 7.80/2.82  tff(c_209, plain, (![B_89, A_90]: (B_89=A_90 | ~r1_tarski(B_89, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.80/2.82  tff(c_220, plain, (![B_5, A_4]: (B_5=A_4 | ~r1_tarski(B_5, A_4) | k4_xboole_0(A_4, B_5)!='#skF_6')), inference(resolution, [status(thm)], [c_198, c_209])).
% 7.80/2.82  tff(c_708, plain, (![A_156]: ('#skF_4'(A_156, '#skF_6')='#skF_6' | k4_xboole_0('#skF_6', '#skF_4'(A_156, '#skF_6'))!='#skF_6' | v2_tex_2('#skF_6', A_156) | ~l1_pre_topc(A_156))), inference(resolution, [status(thm)], [c_705, c_220])).
% 7.80/2.82  tff(c_731, plain, (![A_157]: ('#skF_4'(A_157, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_157) | ~l1_pre_topc(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_708])).
% 7.80/2.82  tff(c_734, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_731, c_52])).
% 7.80/2.82  tff(c_737, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_734])).
% 7.80/2.82  tff(c_60, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.80/2.82  tff(c_637, plain, (![A_149, B_150]: (m1_subset_1('#skF_4'(A_149, B_150), k1_zfmisc_1(u1_struct_0(A_149))) | v2_tex_2(B_150, A_149) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.80/2.82  tff(c_38, plain, (![B_38, A_36]: (v3_pre_topc(B_38, A_36) | ~v1_xboole_0(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.80/2.82  tff(c_2229, plain, (![A_244, B_245]: (v3_pre_topc('#skF_4'(A_244, B_245), A_244) | ~v1_xboole_0('#skF_4'(A_244, B_245)) | ~v2_pre_topc(A_244) | v2_tex_2(B_245, A_244) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_244))) | ~l1_pre_topc(A_244))), inference(resolution, [status(thm)], [c_637, c_38])).
% 7.80/2.82  tff(c_2907, plain, (![A_288]: (v3_pre_topc('#skF_4'(A_288, '#skF_6'), A_288) | ~v1_xboole_0('#skF_4'(A_288, '#skF_6')) | ~v2_pre_topc(A_288) | v2_tex_2('#skF_6', A_288) | ~l1_pre_topc(A_288))), inference(resolution, [status(thm)], [c_78, c_2229])).
% 7.80/2.82  tff(c_2910, plain, (v3_pre_topc('#skF_6', '#skF_5') | ~v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_5') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_737, c_2907])).
% 7.80/2.82  tff(c_2912, plain, (v3_pre_topc('#skF_6', '#skF_5') | v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_56, c_737, c_2910])).
% 7.80/2.82  tff(c_2913, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_2912])).
% 7.80/2.82  tff(c_18, plain, (![A_8]: (m1_subset_1('#skF_1'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/2.82  tff(c_273, plain, (![A_92, B_93, C_94]: (k9_subset_1(A_92, B_93, B_93)=B_93 | ~m1_subset_1(C_94, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.80/2.82  tff(c_282, plain, (![A_92, B_93]: (k9_subset_1(A_92, B_93, B_93)=B_93)), inference(resolution, [status(thm)], [c_18, c_273])).
% 7.80/2.82  tff(c_874, plain, (![A_168, B_169, D_170]: (k9_subset_1(u1_struct_0(A_168), B_169, D_170)!='#skF_4'(A_168, B_169) | ~v3_pre_topc(D_170, A_168) | ~m1_subset_1(D_170, k1_zfmisc_1(u1_struct_0(A_168))) | v2_tex_2(B_169, A_168) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.80/2.82  tff(c_7166, plain, (![A_496, B_497]: ('#skF_4'(A_496, B_497)!=B_497 | ~v3_pre_topc(B_497, A_496) | ~m1_subset_1(B_497, k1_zfmisc_1(u1_struct_0(A_496))) | v2_tex_2(B_497, A_496) | ~m1_subset_1(B_497, k1_zfmisc_1(u1_struct_0(A_496))) | ~l1_pre_topc(A_496))), inference(superposition, [status(thm), theory('equality')], [c_282, c_874])).
% 7.80/2.82  tff(c_7194, plain, (![A_496]: ('#skF_4'(A_496, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_496) | v2_tex_2('#skF_6', A_496) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_496))) | ~l1_pre_topc(A_496))), inference(resolution, [status(thm)], [c_78, c_7166])).
% 7.80/2.82  tff(c_7213, plain, (![A_498]: ('#skF_4'(A_498, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_498) | v2_tex_2('#skF_6', A_498) | ~l1_pre_topc(A_498))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7194])).
% 7.80/2.82  tff(c_7216, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2913, c_7213])).
% 7.80/2.82  tff(c_7222, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_737, c_7216])).
% 7.80/2.82  tff(c_7224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_7222])).
% 7.80/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.82  
% 7.80/2.82  Inference rules
% 7.80/2.82  ----------------------
% 7.80/2.82  #Ref     : 2
% 7.80/2.82  #Sup     : 1659
% 7.80/2.82  #Fact    : 0
% 7.80/2.82  #Define  : 0
% 7.80/2.82  #Split   : 10
% 7.80/2.82  #Chain   : 0
% 7.80/2.82  #Close   : 0
% 7.80/2.82  
% 7.80/2.82  Ordering : KBO
% 7.80/2.82  
% 7.80/2.82  Simplification rules
% 7.80/2.82  ----------------------
% 7.80/2.82  #Subsume      : 492
% 7.80/2.82  #Demod        : 1010
% 7.80/2.82  #Tautology    : 465
% 7.80/2.82  #SimpNegUnit  : 37
% 7.80/2.82  #BackRed      : 5
% 7.80/2.82  
% 7.80/2.82  #Partial instantiations: 0
% 7.80/2.82  #Strategies tried      : 1
% 7.80/2.82  
% 7.80/2.82  Timing (in seconds)
% 7.80/2.82  ----------------------
% 7.80/2.82  Preprocessing        : 0.31
% 7.80/2.82  Parsing              : 0.17
% 7.80/2.82  CNF conversion       : 0.02
% 7.80/2.82  Main loop            : 1.74
% 7.80/2.82  Inferencing          : 0.54
% 7.80/2.82  Reduction            : 0.50
% 7.80/2.82  Demodulation         : 0.34
% 7.80/2.82  BG Simplification    : 0.06
% 7.80/2.82  Subsumption          : 0.53
% 7.80/2.82  Abstraction          : 0.07
% 7.80/2.82  MUC search           : 0.00
% 7.80/2.82  Cooper               : 0.00
% 7.80/2.82  Total                : 2.08
% 7.80/2.82  Index Insertion      : 0.00
% 7.80/2.82  Index Deletion       : 0.00
% 7.80/2.82  Index Matching       : 0.00
% 7.80/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
