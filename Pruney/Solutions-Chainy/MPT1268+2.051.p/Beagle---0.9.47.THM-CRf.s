%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:53 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 143 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  152 ( 426 expanded)
%              Number of equality atoms :   27 (  65 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_49,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_314,plain,(
    ! [B_66,A_67] :
      ( v2_tops_1(B_66,A_67)
      | k1_tops_1(A_67,B_66) != k1_xboole_0
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_321,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_314])).

tff(c_325,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_321])).

tff(c_326,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_325])).

tff(c_56,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_56])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_141,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tops_1(A_53,B_54),B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_146,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_141])).

tff(c_150,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_146])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_445,plain,(
    ! [A_78,B_79] :
      ( v3_pre_topc(k1_tops_1(A_78,B_79),A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_450,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_445])).

tff(c_454,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_450])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_43,B_2,A_1] :
      ( r1_tarski(A_43,B_2)
      | ~ r1_tarski(A_43,A_1)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_83])).

tff(c_158,plain,(
    ! [B_2] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_2)
      | k4_xboole_0('#skF_2',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_150,c_89])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [C_32] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_32
      | ~ v3_pre_topc(C_32,'#skF_1')
      | ~ r1_tarski(C_32,'#skF_2')
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_173,plain,(
    ! [C_55] :
      ( k1_xboole_0 = C_55
      | ~ v3_pre_topc(C_55,'#skF_1')
      | ~ r1_tarski(C_55,'#skF_2')
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_48])).

tff(c_517,plain,(
    ! [A_86] :
      ( k1_xboole_0 = A_86
      | ~ v3_pre_topc(A_86,'#skF_1')
      | ~ r1_tarski(A_86,'#skF_2')
      | ~ r1_tarski(A_86,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_173])).

tff(c_531,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_158,c_517])).

tff(c_547,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_150,c_454,c_531])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_547])).

tff(c_550,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_551,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_36,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_557,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_36])).

tff(c_681,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(k1_tops_1(A_106,B_107),B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_686,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_557,c_681])).

tff(c_692,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_686])).

tff(c_706,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_692,c_4])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_720,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_8])).

tff(c_724,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_550,c_720])).

tff(c_32,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_553,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_32])).

tff(c_34,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_555,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_34])).

tff(c_927,plain,(
    ! [A_117,B_118] :
      ( k1_tops_1(A_117,B_118) = k1_xboole_0
      | ~ v2_tops_1(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_937,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_927])).

tff(c_944,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_551,c_937])).

tff(c_1031,plain,(
    ! [B_123,A_124,C_125] :
      ( r1_tarski(B_123,k1_tops_1(A_124,C_125))
      | ~ r1_tarski(B_123,C_125)
      | ~ v3_pre_topc(B_123,A_124)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1038,plain,(
    ! [B_123] :
      ( r1_tarski(B_123,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_123,'#skF_2')
      | ~ v3_pre_topc(B_123,'#skF_1')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_1031])).

tff(c_1049,plain,(
    ! [B_128] :
      ( r1_tarski(B_128,k1_xboole_0)
      | ~ r1_tarski(B_128,'#skF_2')
      | ~ v3_pre_topc(B_128,'#skF_1')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_944,c_1038])).

tff(c_1056,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_557,c_1049])).

tff(c_1063,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_555,c_1056])).

tff(c_1065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_724,c_1063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.47  
% 3.23/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.47  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.47  
% 3.23/1.47  %Foreground sorts:
% 3.23/1.47  
% 3.23/1.47  
% 3.23/1.47  %Background operators:
% 3.23/1.47  
% 3.23/1.47  
% 3.23/1.47  %Foreground operators:
% 3.23/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.47  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.23/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.23/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.23/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.23/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.47  
% 3.29/1.49  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.29/1.49  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.29/1.49  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.29/1.49  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.29/1.49  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.29/1.49  tff(f_51, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.29/1.49  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.29/1.49  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.29/1.49  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.29/1.49  tff(c_30, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.49  tff(c_49, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.29/1.49  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.49  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.49  tff(c_314, plain, (![B_66, A_67]: (v2_tops_1(B_66, A_67) | k1_tops_1(A_67, B_66)!=k1_xboole_0 | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.29/1.49  tff(c_321, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_314])).
% 3.29/1.49  tff(c_325, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_321])).
% 3.29/1.49  tff(c_326, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_49, c_325])).
% 3.29/1.49  tff(c_56, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.49  tff(c_60, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_56])).
% 3.29/1.49  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.49  tff(c_64, plain, (k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_4])).
% 3.29/1.49  tff(c_141, plain, (![A_53, B_54]: (r1_tarski(k1_tops_1(A_53, B_54), B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.29/1.49  tff(c_146, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_141])).
% 3.29/1.49  tff(c_150, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_146])).
% 3.29/1.49  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.49  tff(c_445, plain, (![A_78, B_79]: (v3_pre_topc(k1_tops_1(A_78, B_79), A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.49  tff(c_450, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_445])).
% 3.29/1.49  tff(c_454, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_450])).
% 3.29/1.49  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.49  tff(c_83, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.49  tff(c_89, plain, (![A_43, B_2, A_1]: (r1_tarski(A_43, B_2) | ~r1_tarski(A_43, A_1) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_83])).
% 3.29/1.49  tff(c_158, plain, (![B_2]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_2) | k4_xboole_0('#skF_2', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_150, c_89])).
% 3.29/1.49  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.49  tff(c_48, plain, (![C_32]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_32 | ~v3_pre_topc(C_32, '#skF_1') | ~r1_tarski(C_32, '#skF_2') | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.49  tff(c_173, plain, (![C_55]: (k1_xboole_0=C_55 | ~v3_pre_topc(C_55, '#skF_1') | ~r1_tarski(C_55, '#skF_2') | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_49, c_48])).
% 3.29/1.49  tff(c_517, plain, (![A_86]: (k1_xboole_0=A_86 | ~v3_pre_topc(A_86, '#skF_1') | ~r1_tarski(A_86, '#skF_2') | ~r1_tarski(A_86, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_173])).
% 3.29/1.49  tff(c_531, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_158, c_517])).
% 3.29/1.49  tff(c_547, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_150, c_454, c_531])).
% 3.29/1.49  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_326, c_547])).
% 3.29/1.49  tff(c_550, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 3.29/1.49  tff(c_551, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.29/1.49  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.49  tff(c_557, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_36])).
% 3.29/1.49  tff(c_681, plain, (![A_106, B_107]: (r1_tarski(k1_tops_1(A_106, B_107), B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.29/1.49  tff(c_686, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_557, c_681])).
% 3.29/1.49  tff(c_692, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_686])).
% 3.29/1.49  tff(c_706, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_692, c_4])).
% 3.29/1.49  tff(c_8, plain, (![A_6, B_7]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k4_xboole_0(B_7, A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.29/1.49  tff(c_720, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_706, c_8])).
% 3.29/1.49  tff(c_724, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_550, c_720])).
% 3.29/1.49  tff(c_32, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.49  tff(c_553, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_551, c_32])).
% 3.29/1.49  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.49  tff(c_555, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_551, c_34])).
% 3.29/1.49  tff(c_927, plain, (![A_117, B_118]: (k1_tops_1(A_117, B_118)=k1_xboole_0 | ~v2_tops_1(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.29/1.49  tff(c_937, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_927])).
% 3.29/1.49  tff(c_944, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_551, c_937])).
% 3.29/1.49  tff(c_1031, plain, (![B_123, A_124, C_125]: (r1_tarski(B_123, k1_tops_1(A_124, C_125)) | ~r1_tarski(B_123, C_125) | ~v3_pre_topc(B_123, A_124) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.29/1.49  tff(c_1038, plain, (![B_123]: (r1_tarski(B_123, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_123, '#skF_2') | ~v3_pre_topc(B_123, '#skF_1') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1031])).
% 3.29/1.49  tff(c_1049, plain, (![B_128]: (r1_tarski(B_128, k1_xboole_0) | ~r1_tarski(B_128, '#skF_2') | ~v3_pre_topc(B_128, '#skF_1') | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_944, c_1038])).
% 3.29/1.49  tff(c_1056, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_557, c_1049])).
% 3.29/1.49  tff(c_1063, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_553, c_555, c_1056])).
% 3.29/1.49  tff(c_1065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_724, c_1063])).
% 3.29/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.49  
% 3.29/1.49  Inference rules
% 3.29/1.49  ----------------------
% 3.29/1.49  #Ref     : 0
% 3.29/1.49  #Sup     : 244
% 3.29/1.49  #Fact    : 0
% 3.29/1.49  #Define  : 0
% 3.29/1.49  #Split   : 10
% 3.29/1.49  #Chain   : 0
% 3.29/1.49  #Close   : 0
% 3.29/1.49  
% 3.29/1.49  Ordering : KBO
% 3.29/1.49  
% 3.29/1.49  Simplification rules
% 3.29/1.49  ----------------------
% 3.29/1.49  #Subsume      : 56
% 3.29/1.49  #Demod        : 61
% 3.29/1.49  #Tautology    : 80
% 3.29/1.49  #SimpNegUnit  : 8
% 3.29/1.49  #BackRed      : 4
% 3.29/1.49  
% 3.29/1.49  #Partial instantiations: 0
% 3.29/1.49  #Strategies tried      : 1
% 3.29/1.49  
% 3.29/1.49  Timing (in seconds)
% 3.29/1.49  ----------------------
% 3.29/1.49  Preprocessing        : 0.31
% 3.29/1.49  Parsing              : 0.17
% 3.29/1.49  CNF conversion       : 0.02
% 3.29/1.49  Main loop            : 0.40
% 3.29/1.49  Inferencing          : 0.14
% 3.29/1.49  Reduction            : 0.11
% 3.29/1.49  Demodulation         : 0.07
% 3.29/1.49  BG Simplification    : 0.02
% 3.29/1.49  Subsumption          : 0.09
% 3.29/1.49  Abstraction          : 0.02
% 3.29/1.49  MUC search           : 0.00
% 3.29/1.49  Cooper               : 0.00
% 3.29/1.49  Total                : 0.74
% 3.29/1.49  Index Insertion      : 0.00
% 3.29/1.49  Index Deletion       : 0.00
% 3.29/1.49  Index Matching       : 0.00
% 3.29/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
