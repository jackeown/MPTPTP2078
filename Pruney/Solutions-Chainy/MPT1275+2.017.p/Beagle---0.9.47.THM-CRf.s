%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:04 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 145 expanded)
%              Number of leaves         :   38 (  68 expanded)
%              Depth                    :    7
%              Number of atoms          :  141 ( 322 expanded)
%              Number of equality atoms :   35 (  71 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_64,plain,
    ( v3_tops_1('#skF_3','#skF_2')
    | k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_69,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,
    ( k2_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_76,plain,(
    ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_58])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_395,plain,(
    ! [A_106,B_107] :
      ( k1_tops_1(A_106,B_107) = k1_xboole_0
      | ~ v2_tops_1(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_406,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_395])).

tff(c_415,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_406])).

tff(c_417,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_542,plain,(
    ! [B_125,A_126] :
      ( v2_tops_1(B_125,A_126)
      | ~ r1_tarski(B_125,k2_tops_1(A_126,B_125))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_550,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_542])).

tff(c_556,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_12,c_550])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_417,c_556])).

tff(c_560,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_52,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_310,plain,(
    ! [A_95,B_96] :
      ( k2_pre_topc(A_95,B_96) = B_96
      | ~ v4_pre_topc(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_317,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_310])).

tff(c_325,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_317])).

tff(c_741,plain,(
    ! [B_147,A_148] :
      ( v3_tops_1(B_147,A_148)
      | ~ v2_tops_1(k2_pre_topc(A_148,B_147),A_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_743,plain,
    ( v3_tops_1('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_741])).

tff(c_745,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_560,c_743])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_745])).

tff(c_749,plain,(
    k2_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_22,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_753,plain,(
    ! [A_151,B_152] :
      ( r1_tarski(A_151,B_152)
      | ~ m1_subset_1(A_151,k1_zfmisc_1(B_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_765,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(resolution,[status(thm)],[c_22,c_753])).

tff(c_867,plain,(
    ! [A_169,B_170] :
      ( k2_xboole_0(A_169,k4_xboole_0(B_170,A_169)) = B_170
      | ~ r1_tarski(A_169,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_767,plain,(
    ! [A_154,B_155] :
      ( k2_xboole_0(A_154,B_155) = B_155
      | ~ r1_tarski(A_154,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_778,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(resolution,[status(thm)],[c_765,c_767])).

tff(c_874,plain,(
    ! [B_170] :
      ( k4_xboole_0(B_170,k1_xboole_0) = B_170
      | ~ r1_tarski(k1_xboole_0,B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_778])).

tff(c_884,plain,(
    ! [B_170] : k4_xboole_0(B_170,k1_xboole_0) = B_170 ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_874])).

tff(c_928,plain,(
    ! [A_184,B_185,C_186] :
      ( k7_subset_1(A_184,B_185,C_186) = k4_xboole_0(B_185,C_186)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(A_184)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_936,plain,(
    ! [C_186] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_186) = k4_xboole_0('#skF_3',C_186) ),
    inference(resolution,[status(thm)],[c_54,c_928])).

tff(c_974,plain,(
    ! [A_193,B_194] :
      ( k2_pre_topc(A_193,B_194) = B_194
      | ~ v4_pre_topc(B_194,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_981,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_974])).

tff(c_989,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_981])).

tff(c_748,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_947,plain,(
    ! [B_189,A_190] :
      ( v2_tops_1(B_189,A_190)
      | ~ v3_tops_1(B_189,A_190)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_954,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ v3_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_947])).

tff(c_962,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_748,c_954])).

tff(c_1047,plain,(
    ! [A_204,B_205] :
      ( k1_tops_1(A_204,B_205) = k1_xboole_0
      | ~ v2_tops_1(B_205,A_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1054,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1047])).

tff(c_1062,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_962,c_1054])).

tff(c_1452,plain,(
    ! [A_241,B_242] :
      ( k7_subset_1(u1_struct_0(A_241),k2_pre_topc(A_241,B_242),k1_tops_1(A_241,B_242)) = k2_tops_1(A_241,B_242)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1464,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),k1_xboole_0) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_1452])).

tff(c_1473,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_884,c_936,c_989,c_1464])).

tff(c_1475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_749,c_1473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:28:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.52  
% 3.38/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.52  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.38/1.52  
% 3.38/1.52  %Foreground sorts:
% 3.38/1.52  
% 3.38/1.52  
% 3.38/1.52  %Background operators:
% 3.38/1.52  
% 3.38/1.52  
% 3.38/1.52  %Foreground operators:
% 3.38/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.52  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.38/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.52  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.38/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.38/1.52  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.38/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.52  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.38/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.52  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.38/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.52  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.38/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.38/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.38/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.38/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.52  
% 3.50/1.53  tff(f_139, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 3.50/1.53  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.50/1.53  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.50/1.53  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.50/1.53  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.50/1.53  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 3.50/1.53  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.50/1.53  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.50/1.53  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 3.50/1.53  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.50/1.53  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.50/1.53  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 3.50/1.53  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.50/1.53  tff(c_64, plain, (v3_tops_1('#skF_3', '#skF_2') | k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.50/1.53  tff(c_69, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_64])).
% 3.50/1.53  tff(c_58, plain, (k2_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~v3_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.50/1.53  tff(c_76, plain, (~v3_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_58])).
% 3.50/1.53  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.50/1.53  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.50/1.53  tff(c_395, plain, (![A_106, B_107]: (k1_tops_1(A_106, B_107)=k1_xboole_0 | ~v2_tops_1(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.50/1.53  tff(c_406, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_395])).
% 3.50/1.53  tff(c_415, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_406])).
% 3.50/1.53  tff(c_417, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_415])).
% 3.50/1.53  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.50/1.53  tff(c_542, plain, (![B_125, A_126]: (v2_tops_1(B_125, A_126) | ~r1_tarski(B_125, k2_tops_1(A_126, B_125)) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.50/1.53  tff(c_550, plain, (v2_tops_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_69, c_542])).
% 3.50/1.53  tff(c_556, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_12, c_550])).
% 3.50/1.53  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_417, c_556])).
% 3.50/1.53  tff(c_560, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_415])).
% 3.50/1.53  tff(c_52, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.50/1.53  tff(c_310, plain, (![A_95, B_96]: (k2_pre_topc(A_95, B_96)=B_96 | ~v4_pre_topc(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.50/1.53  tff(c_317, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_310])).
% 3.50/1.53  tff(c_325, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_317])).
% 3.50/1.53  tff(c_741, plain, (![B_147, A_148]: (v3_tops_1(B_147, A_148) | ~v2_tops_1(k2_pre_topc(A_148, B_147), A_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.50/1.53  tff(c_743, plain, (v3_tops_1('#skF_3', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_325, c_741])).
% 3.50/1.53  tff(c_745, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_560, c_743])).
% 3.50/1.53  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_745])).
% 3.50/1.53  tff(c_749, plain, (k2_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_64])).
% 3.50/1.53  tff(c_22, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.50/1.53  tff(c_753, plain, (![A_151, B_152]: (r1_tarski(A_151, B_152) | ~m1_subset_1(A_151, k1_zfmisc_1(B_152)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.50/1.53  tff(c_765, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_22, c_753])).
% 3.50/1.53  tff(c_867, plain, (![A_169, B_170]: (k2_xboole_0(A_169, k4_xboole_0(B_170, A_169))=B_170 | ~r1_tarski(A_169, B_170))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.53  tff(c_767, plain, (![A_154, B_155]: (k2_xboole_0(A_154, B_155)=B_155 | ~r1_tarski(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.50/1.53  tff(c_778, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(resolution, [status(thm)], [c_765, c_767])).
% 3.50/1.53  tff(c_874, plain, (![B_170]: (k4_xboole_0(B_170, k1_xboole_0)=B_170 | ~r1_tarski(k1_xboole_0, B_170))), inference(superposition, [status(thm), theory('equality')], [c_867, c_778])).
% 3.50/1.53  tff(c_884, plain, (![B_170]: (k4_xboole_0(B_170, k1_xboole_0)=B_170)), inference(demodulation, [status(thm), theory('equality')], [c_765, c_874])).
% 3.50/1.53  tff(c_928, plain, (![A_184, B_185, C_186]: (k7_subset_1(A_184, B_185, C_186)=k4_xboole_0(B_185, C_186) | ~m1_subset_1(B_185, k1_zfmisc_1(A_184)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.50/1.53  tff(c_936, plain, (![C_186]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_186)=k4_xboole_0('#skF_3', C_186))), inference(resolution, [status(thm)], [c_54, c_928])).
% 3.50/1.53  tff(c_974, plain, (![A_193, B_194]: (k2_pre_topc(A_193, B_194)=B_194 | ~v4_pre_topc(B_194, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.50/1.53  tff(c_981, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_974])).
% 3.50/1.53  tff(c_989, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_981])).
% 3.50/1.53  tff(c_748, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 3.50/1.53  tff(c_947, plain, (![B_189, A_190]: (v2_tops_1(B_189, A_190) | ~v3_tops_1(B_189, A_190) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.50/1.53  tff(c_954, plain, (v2_tops_1('#skF_3', '#skF_2') | ~v3_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_947])).
% 3.50/1.53  tff(c_962, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_748, c_954])).
% 3.50/1.53  tff(c_1047, plain, (![A_204, B_205]: (k1_tops_1(A_204, B_205)=k1_xboole_0 | ~v2_tops_1(B_205, A_204) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.50/1.53  tff(c_1054, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1047])).
% 3.50/1.53  tff(c_1062, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_962, c_1054])).
% 3.50/1.53  tff(c_1452, plain, (![A_241, B_242]: (k7_subset_1(u1_struct_0(A_241), k2_pre_topc(A_241, B_242), k1_tops_1(A_241, B_242))=k2_tops_1(A_241, B_242) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.50/1.53  tff(c_1464, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), k1_xboole_0)=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1062, c_1452])).
% 3.50/1.53  tff(c_1473, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_884, c_936, c_989, c_1464])).
% 3.50/1.53  tff(c_1475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_749, c_1473])).
% 3.50/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.53  
% 3.50/1.53  Inference rules
% 3.50/1.53  ----------------------
% 3.50/1.53  #Ref     : 0
% 3.50/1.53  #Sup     : 303
% 3.50/1.53  #Fact    : 0
% 3.50/1.53  #Define  : 0
% 3.50/1.53  #Split   : 8
% 3.50/1.53  #Chain   : 0
% 3.50/1.53  #Close   : 0
% 3.50/1.53  
% 3.50/1.53  Ordering : KBO
% 3.50/1.53  
% 3.50/1.53  Simplification rules
% 3.50/1.53  ----------------------
% 3.50/1.53  #Subsume      : 21
% 3.50/1.53  #Demod        : 107
% 3.50/1.53  #Tautology    : 119
% 3.50/1.53  #SimpNegUnit  : 6
% 3.50/1.53  #BackRed      : 4
% 3.50/1.53  
% 3.50/1.53  #Partial instantiations: 0
% 3.50/1.53  #Strategies tried      : 1
% 3.50/1.53  
% 3.50/1.53  Timing (in seconds)
% 3.50/1.53  ----------------------
% 3.50/1.54  Preprocessing        : 0.33
% 3.50/1.54  Parsing              : 0.17
% 3.50/1.54  CNF conversion       : 0.02
% 3.50/1.54  Main loop            : 0.45
% 3.50/1.54  Inferencing          : 0.17
% 3.50/1.54  Reduction            : 0.13
% 3.50/1.54  Demodulation         : 0.09
% 3.50/1.54  BG Simplification    : 0.02
% 3.50/1.54  Subsumption          : 0.09
% 3.50/1.54  Abstraction          : 0.02
% 3.50/1.54  MUC search           : 0.00
% 3.50/1.54  Cooper               : 0.00
% 3.50/1.54  Total                : 0.82
% 3.50/1.54  Index Insertion      : 0.00
% 3.50/1.54  Index Deletion       : 0.00
% 3.50/1.54  Index Matching       : 0.00
% 3.50/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
