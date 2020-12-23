%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:50 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 137 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  151 ( 391 expanded)
%              Number of equality atoms :   22 (  54 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_76,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_36,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_57,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_612,plain,(
    ! [B_95,A_96] :
      ( v2_tops_1(B_95,A_96)
      | k1_tops_1(A_96,B_95) != k1_xboole_0
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_619,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_612])).

tff(c_623,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_619])).

tff(c_624,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_623])).

tff(c_203,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tops_1(A_62,B_63),B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_208,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_203])).

tff(c_212,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_208])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_436,plain,(
    ! [A_84,B_85] :
      ( v3_pre_topc(k1_tops_1(A_84,B_85),A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_441,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_436])).

tff(c_445,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_441])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_74,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_143,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(A_53,C_54)
      | ~ r1_tarski(B_55,C_54)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_172,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_58,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_74,c_143])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_558,plain,(
    ! [A_93,A_94] :
      ( r1_tarski(A_93,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_93,A_94)
      | ~ r1_tarski(A_94,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_172,c_10])).

tff(c_574,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_212,c_558])).

tff(c_604,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_574])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [C_36] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_36
      | ~ v3_pre_topc(C_36,'#skF_1')
      | ~ r1_tarski(C_36,'#skF_2')
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_508,plain,(
    ! [C_89] :
      ( k1_xboole_0 = C_89
      | ~ v3_pre_topc(C_89,'#skF_1')
      | ~ r1_tarski(C_89,'#skF_2')
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_54])).

tff(c_818,plain,(
    ! [A_109] :
      ( k1_xboole_0 = A_109
      | ~ v3_pre_topc(A_109,'#skF_1')
      | ~ r1_tarski(A_109,'#skF_2')
      | ~ r1_tarski(A_109,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_508])).

tff(c_836,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_604,c_818])).

tff(c_877,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_445,c_836])).

tff(c_879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_877])).

tff(c_880,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_881,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_897,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_38])).

tff(c_40,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_884,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_40])).

tff(c_42,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_904,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_42])).

tff(c_1254,plain,(
    ! [A_150,B_151] :
      ( k1_tops_1(A_150,B_151) = k1_xboole_0
      | ~ v2_tops_1(B_151,A_150)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1264,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1254])).

tff(c_1271,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_881,c_1264])).

tff(c_1492,plain,(
    ! [B_166,A_167,C_168] :
      ( r1_tarski(B_166,k1_tops_1(A_167,C_168))
      | ~ r1_tarski(B_166,C_168)
      | ~ v3_pre_topc(B_166,A_167)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1499,plain,(
    ! [B_166] :
      ( r1_tarski(B_166,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_166,'#skF_2')
      | ~ v3_pre_topc(B_166,'#skF_1')
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1492])).

tff(c_1527,plain,(
    ! [B_171] :
      ( r1_tarski(B_171,k1_xboole_0)
      | ~ r1_tarski(B_171,'#skF_2')
      | ~ v3_pre_topc(B_171,'#skF_1')
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1271,c_1499])).

tff(c_1534,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_904,c_1527])).

tff(c_1541,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_884,c_1534])).

tff(c_885,plain,(
    ! [A_112,B_113] : k4_xboole_0(A_112,k2_xboole_0(A_112,B_113)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_890,plain,(
    ! [A_112] : r1_tarski(k1_xboole_0,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_12])).

tff(c_923,plain,(
    ! [B_121,A_122] :
      ( B_121 = A_122
      | ~ r1_tarski(B_121,A_122)
      | ~ r1_tarski(A_122,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_938,plain,(
    ! [A_112] :
      ( k1_xboole_0 = A_112
      | ~ r1_tarski(A_112,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_890,c_923])).

tff(c_1551,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1541,c_938])).

tff(c_1563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_880,c_1551])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:03:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.56  
% 3.65/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.56  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.65/1.56  
% 3.65/1.56  %Foreground sorts:
% 3.65/1.56  
% 3.65/1.56  
% 3.65/1.56  %Background operators:
% 3.65/1.56  
% 3.65/1.56  
% 3.65/1.56  %Foreground operators:
% 3.65/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.65/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.65/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.65/1.56  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.65/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.65/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.65/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.65/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.65/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.65/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.65/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.65/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.65/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.65/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.65/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.56  
% 3.77/1.58  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.77/1.58  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.77/1.58  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.77/1.58  tff(f_55, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.77/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.77/1.58  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.77/1.58  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.77/1.58  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.77/1.58  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.77/1.58  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.77/1.58  tff(c_36, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.77/1.58  tff(c_57, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.77/1.58  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.77/1.58  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.77/1.58  tff(c_612, plain, (![B_95, A_96]: (v2_tops_1(B_95, A_96) | k1_tops_1(A_96, B_95)!=k1_xboole_0 | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.77/1.58  tff(c_619, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_612])).
% 3.77/1.58  tff(c_623, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_619])).
% 3.77/1.58  tff(c_624, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_57, c_623])).
% 3.77/1.58  tff(c_203, plain, (![A_62, B_63]: (r1_tarski(k1_tops_1(A_62, B_63), B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.58  tff(c_208, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_203])).
% 3.77/1.58  tff(c_212, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_208])).
% 3.77/1.58  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.77/1.58  tff(c_436, plain, (![A_84, B_85]: (v3_pre_topc(k1_tops_1(A_84, B_85), A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.77/1.58  tff(c_441, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_436])).
% 3.77/1.58  tff(c_445, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_441])).
% 3.77/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.58  tff(c_70, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.77/1.58  tff(c_74, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_70])).
% 3.77/1.58  tff(c_143, plain, (![A_53, C_54, B_55]: (r1_tarski(A_53, C_54) | ~r1_tarski(B_55, C_54) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.77/1.58  tff(c_172, plain, (![A_58]: (r1_tarski(A_58, u1_struct_0('#skF_1')) | ~r1_tarski(A_58, '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_143])).
% 3.77/1.58  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.77/1.58  tff(c_558, plain, (![A_93, A_94]: (r1_tarski(A_93, u1_struct_0('#skF_1')) | ~r1_tarski(A_93, A_94) | ~r1_tarski(A_94, '#skF_2'))), inference(resolution, [status(thm)], [c_172, c_10])).
% 3.77/1.58  tff(c_574, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_212, c_558])).
% 3.77/1.58  tff(c_604, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_574])).
% 3.77/1.58  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.77/1.58  tff(c_54, plain, (![C_36]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_36 | ~v3_pre_topc(C_36, '#skF_1') | ~r1_tarski(C_36, '#skF_2') | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.77/1.58  tff(c_508, plain, (![C_89]: (k1_xboole_0=C_89 | ~v3_pre_topc(C_89, '#skF_1') | ~r1_tarski(C_89, '#skF_2') | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_57, c_54])).
% 3.77/1.58  tff(c_818, plain, (![A_109]: (k1_xboole_0=A_109 | ~v3_pre_topc(A_109, '#skF_1') | ~r1_tarski(A_109, '#skF_2') | ~r1_tarski(A_109, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_508])).
% 3.77/1.58  tff(c_836, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_604, c_818])).
% 3.77/1.58  tff(c_877, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_212, c_445, c_836])).
% 3.77/1.58  tff(c_879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_624, c_877])).
% 3.77/1.58  tff(c_880, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.77/1.58  tff(c_881, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.77/1.58  tff(c_38, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.77/1.58  tff(c_897, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_881, c_38])).
% 3.77/1.58  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.77/1.58  tff(c_884, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_881, c_40])).
% 3.77/1.58  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.77/1.58  tff(c_904, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_881, c_42])).
% 3.77/1.58  tff(c_1254, plain, (![A_150, B_151]: (k1_tops_1(A_150, B_151)=k1_xboole_0 | ~v2_tops_1(B_151, A_150) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.77/1.58  tff(c_1264, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1254])).
% 3.77/1.58  tff(c_1271, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_881, c_1264])).
% 3.77/1.58  tff(c_1492, plain, (![B_166, A_167, C_168]: (r1_tarski(B_166, k1_tops_1(A_167, C_168)) | ~r1_tarski(B_166, C_168) | ~v3_pre_topc(B_166, A_167) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.77/1.58  tff(c_1499, plain, (![B_166]: (r1_tarski(B_166, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_166, '#skF_2') | ~v3_pre_topc(B_166, '#skF_1') | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1492])).
% 3.77/1.58  tff(c_1527, plain, (![B_171]: (r1_tarski(B_171, k1_xboole_0) | ~r1_tarski(B_171, '#skF_2') | ~v3_pre_topc(B_171, '#skF_1') | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1271, c_1499])).
% 3.77/1.58  tff(c_1534, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_904, c_1527])).
% 3.77/1.58  tff(c_1541, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_897, c_884, c_1534])).
% 3.77/1.58  tff(c_885, plain, (![A_112, B_113]: (k4_xboole_0(A_112, k2_xboole_0(A_112, B_113))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.77/1.58  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.77/1.58  tff(c_890, plain, (![A_112]: (r1_tarski(k1_xboole_0, A_112))), inference(superposition, [status(thm), theory('equality')], [c_885, c_12])).
% 3.77/1.58  tff(c_923, plain, (![B_121, A_122]: (B_121=A_122 | ~r1_tarski(B_121, A_122) | ~r1_tarski(A_122, B_121))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.58  tff(c_938, plain, (![A_112]: (k1_xboole_0=A_112 | ~r1_tarski(A_112, k1_xboole_0))), inference(resolution, [status(thm)], [c_890, c_923])).
% 3.77/1.58  tff(c_1551, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1541, c_938])).
% 3.77/1.58  tff(c_1563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_880, c_1551])).
% 3.77/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.58  
% 3.77/1.58  Inference rules
% 3.77/1.58  ----------------------
% 3.77/1.58  #Ref     : 0
% 3.77/1.58  #Sup     : 342
% 3.77/1.58  #Fact    : 0
% 3.77/1.58  #Define  : 0
% 3.77/1.58  #Split   : 13
% 3.77/1.58  #Chain   : 0
% 3.77/1.58  #Close   : 0
% 3.77/1.58  
% 3.77/1.58  Ordering : KBO
% 3.77/1.58  
% 3.77/1.58  Simplification rules
% 3.77/1.58  ----------------------
% 3.77/1.58  #Subsume      : 73
% 3.77/1.58  #Demod        : 212
% 3.77/1.58  #Tautology    : 119
% 3.77/1.58  #SimpNegUnit  : 5
% 3.77/1.58  #BackRed      : 4
% 3.77/1.58  
% 3.77/1.58  #Partial instantiations: 0
% 3.77/1.58  #Strategies tried      : 1
% 3.77/1.58  
% 3.77/1.58  Timing (in seconds)
% 3.77/1.58  ----------------------
% 3.77/1.58  Preprocessing        : 0.34
% 3.77/1.58  Parsing              : 0.17
% 3.77/1.58  CNF conversion       : 0.02
% 3.77/1.58  Main loop            : 0.48
% 3.77/1.58  Inferencing          : 0.16
% 3.77/1.58  Reduction            : 0.16
% 3.77/1.58  Demodulation         : 0.12
% 3.77/1.58  BG Simplification    : 0.02
% 3.77/1.58  Subsumption          : 0.10
% 3.77/1.58  Abstraction          : 0.02
% 3.77/1.58  MUC search           : 0.00
% 3.77/1.58  Cooper               : 0.00
% 3.77/1.58  Total                : 0.85
% 3.77/1.58  Index Insertion      : 0.00
% 3.77/1.58  Index Deletion       : 0.00
% 3.77/1.58  Index Matching       : 0.00
% 3.77/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
