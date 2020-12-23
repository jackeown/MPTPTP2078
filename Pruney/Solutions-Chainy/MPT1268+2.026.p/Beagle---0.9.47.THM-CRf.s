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

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 128 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  149 ( 356 expanded)
%              Number of equality atoms :   29 (  58 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
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

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_55,axiom,(
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

tff(f_84,axiom,(
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

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_79,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1329,plain,(
    ! [B_109,A_110] :
      ( v2_tops_1(B_109,A_110)
      | k1_tops_1(A_110,B_109) != k1_xboole_0
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1336,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1329])).

tff(c_1340,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1336])).

tff(c_1341,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_1340])).

tff(c_647,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(k1_tops_1(A_87,B_88),B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_652,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_647])).

tff(c_656,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_652])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1056,plain,(
    ! [A_102,B_103] :
      ( v3_pre_topc(k1_tops_1(A_102,B_103),A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1061,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1056])).

tff(c_1065,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1061])).

tff(c_114,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_122,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_114])).

tff(c_363,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_376,plain,(
    ! [A_68] :
      ( r1_tarski(A_68,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_68,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_122,c_363])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,(
    ! [C_40] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_40
      | ~ v3_pre_topc(C_40,'#skF_1')
      | ~ r1_tarski(C_40,'#skF_2')
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_258,plain,(
    ! [C_63] :
      ( k1_xboole_0 = C_63
      | ~ v3_pre_topc(C_63,'#skF_1')
      | ~ r1_tarski(C_63,'#skF_2')
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_60])).

tff(c_1449,plain,(
    ! [A_112] :
      ( k1_xboole_0 = A_112
      | ~ v3_pre_topc(A_112,'#skF_1')
      | ~ r1_tarski(A_112,'#skF_2')
      | ~ r1_tarski(A_112,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_258])).

tff(c_1503,plain,(
    ! [A_113] :
      ( k1_xboole_0 = A_113
      | ~ v3_pre_topc(A_113,'#skF_1')
      | ~ r1_tarski(A_113,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_376,c_1449])).

tff(c_1506,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1065,c_1503])).

tff(c_1509,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_1506])).

tff(c_1511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1341,c_1509])).

tff(c_1512,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1513,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1520,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1513,c_44])).

tff(c_46,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1522,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1513,c_46])).

tff(c_48,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1541,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1513,c_48])).

tff(c_2922,plain,(
    ! [A_182,B_183] :
      ( k1_tops_1(A_182,B_183) = k1_xboole_0
      | ~ v2_tops_1(B_183,A_182)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2932,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2922])).

tff(c_2940,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1513,c_2932])).

tff(c_3593,plain,(
    ! [B_192,A_193,C_194] :
      ( r1_tarski(B_192,k1_tops_1(A_193,C_194))
      | ~ r1_tarski(B_192,C_194)
      | ~ v3_pre_topc(B_192,A_193)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3600,plain,(
    ! [B_192] :
      ( r1_tarski(B_192,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_192,'#skF_2')
      | ~ v3_pre_topc(B_192,'#skF_1')
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_3593])).

tff(c_3734,plain,(
    ! [B_196] :
      ( r1_tarski(B_196,k1_xboole_0)
      | ~ r1_tarski(B_196,'#skF_2')
      | ~ v3_pre_topc(B_196,'#skF_1')
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2940,c_3600])).

tff(c_3741,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1541,c_3734])).

tff(c_3748,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_1522,c_3741])).

tff(c_14,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1675,plain,(
    ! [A_127,B_128] : k4_xboole_0(A_127,k4_xboole_0(A_127,B_128)) = k3_xboole_0(A_127,B_128) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1702,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1675])).

tff(c_1713,plain,(
    ! [A_129] : k4_xboole_0(A_129,A_129) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1702])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1721,plain,(
    ! [A_129] : r1_tarski(k1_xboole_0,A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_1713,c_16])).

tff(c_1885,plain,(
    ! [B_136,A_137] :
      ( B_136 = A_137
      | ~ r1_tarski(B_136,A_137)
      | ~ r1_tarski(A_137,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1901,plain,(
    ! [A_129] :
      ( k1_xboole_0 = A_129
      | ~ r1_tarski(A_129,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1721,c_1885])).

tff(c_3758,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3748,c_1901])).

tff(c_3769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1512,c_3758])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.81  
% 4.14/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.81  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.14/1.81  
% 4.14/1.81  %Foreground sorts:
% 4.14/1.81  
% 4.14/1.81  
% 4.14/1.81  %Background operators:
% 4.14/1.81  
% 4.14/1.81  
% 4.14/1.81  %Foreground operators:
% 4.14/1.81  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.14/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.14/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.81  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.14/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.14/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.14/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.81  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.14/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.14/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.14/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.14/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.14/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.14/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.14/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.14/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.14/1.81  
% 4.35/1.84  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 4.35/1.84  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.35/1.84  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.35/1.84  tff(f_63, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.35/1.84  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.35/1.84  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.35/1.84  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 4.35/1.84  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.35/1.84  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.35/1.84  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.35/1.84  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.35/1.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.35/1.84  tff(c_42, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.35/1.84  tff(c_79, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 4.35/1.84  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.35/1.84  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.35/1.84  tff(c_1329, plain, (![B_109, A_110]: (v2_tops_1(B_109, A_110) | k1_tops_1(A_110, B_109)!=k1_xboole_0 | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.35/1.84  tff(c_1336, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1329])).
% 4.35/1.84  tff(c_1340, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1336])).
% 4.35/1.84  tff(c_1341, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_79, c_1340])).
% 4.35/1.84  tff(c_647, plain, (![A_87, B_88]: (r1_tarski(k1_tops_1(A_87, B_88), B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.35/1.84  tff(c_652, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_647])).
% 4.35/1.84  tff(c_656, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_652])).
% 4.35/1.84  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.35/1.84  tff(c_1056, plain, (![A_102, B_103]: (v3_pre_topc(k1_tops_1(A_102, B_103), A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.35/1.84  tff(c_1061, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1056])).
% 4.35/1.84  tff(c_1065, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1061])).
% 4.35/1.84  tff(c_114, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.35/1.84  tff(c_122, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_114])).
% 4.35/1.84  tff(c_363, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.35/1.84  tff(c_376, plain, (![A_68]: (r1_tarski(A_68, u1_struct_0('#skF_1')) | ~r1_tarski(A_68, '#skF_2'))), inference(resolution, [status(thm)], [c_122, c_363])).
% 4.35/1.84  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.35/1.84  tff(c_60, plain, (![C_40]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_40 | ~v3_pre_topc(C_40, '#skF_1') | ~r1_tarski(C_40, '#skF_2') | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.35/1.84  tff(c_258, plain, (![C_63]: (k1_xboole_0=C_63 | ~v3_pre_topc(C_63, '#skF_1') | ~r1_tarski(C_63, '#skF_2') | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_79, c_60])).
% 4.35/1.84  tff(c_1449, plain, (![A_112]: (k1_xboole_0=A_112 | ~v3_pre_topc(A_112, '#skF_1') | ~r1_tarski(A_112, '#skF_2') | ~r1_tarski(A_112, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_258])).
% 4.35/1.84  tff(c_1503, plain, (![A_113]: (k1_xboole_0=A_113 | ~v3_pre_topc(A_113, '#skF_1') | ~r1_tarski(A_113, '#skF_2'))), inference(resolution, [status(thm)], [c_376, c_1449])).
% 4.35/1.84  tff(c_1506, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1065, c_1503])).
% 4.35/1.84  tff(c_1509, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_656, c_1506])).
% 4.35/1.84  tff(c_1511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1341, c_1509])).
% 4.35/1.84  tff(c_1512, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 4.35/1.84  tff(c_1513, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.35/1.84  tff(c_44, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.35/1.84  tff(c_1520, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1513, c_44])).
% 4.35/1.84  tff(c_46, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.35/1.84  tff(c_1522, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1513, c_46])).
% 4.35/1.84  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.35/1.84  tff(c_1541, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1513, c_48])).
% 4.35/1.84  tff(c_2922, plain, (![A_182, B_183]: (k1_tops_1(A_182, B_183)=k1_xboole_0 | ~v2_tops_1(B_183, A_182) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.35/1.84  tff(c_2932, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2922])).
% 4.35/1.84  tff(c_2940, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1513, c_2932])).
% 4.35/1.84  tff(c_3593, plain, (![B_192, A_193, C_194]: (r1_tarski(B_192, k1_tops_1(A_193, C_194)) | ~r1_tarski(B_192, C_194) | ~v3_pre_topc(B_192, A_193) | ~m1_subset_1(C_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.35/1.84  tff(c_3600, plain, (![B_192]: (r1_tarski(B_192, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_192, '#skF_2') | ~v3_pre_topc(B_192, '#skF_1') | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_3593])).
% 4.35/1.84  tff(c_3734, plain, (![B_196]: (r1_tarski(B_196, k1_xboole_0) | ~r1_tarski(B_196, '#skF_2') | ~v3_pre_topc(B_196, '#skF_1') | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2940, c_3600])).
% 4.35/1.84  tff(c_3741, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1541, c_3734])).
% 4.35/1.84  tff(c_3748, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_1522, c_3741])).
% 4.35/1.84  tff(c_14, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.35/1.84  tff(c_18, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.35/1.84  tff(c_1675, plain, (![A_127, B_128]: (k4_xboole_0(A_127, k4_xboole_0(A_127, B_128))=k3_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.35/1.84  tff(c_1702, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1675])).
% 4.35/1.84  tff(c_1713, plain, (![A_129]: (k4_xboole_0(A_129, A_129)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1702])).
% 4.35/1.84  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.35/1.84  tff(c_1721, plain, (![A_129]: (r1_tarski(k1_xboole_0, A_129))), inference(superposition, [status(thm), theory('equality')], [c_1713, c_16])).
% 4.35/1.84  tff(c_1885, plain, (![B_136, A_137]: (B_136=A_137 | ~r1_tarski(B_136, A_137) | ~r1_tarski(A_137, B_136))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.35/1.84  tff(c_1901, plain, (![A_129]: (k1_xboole_0=A_129 | ~r1_tarski(A_129, k1_xboole_0))), inference(resolution, [status(thm)], [c_1721, c_1885])).
% 4.35/1.84  tff(c_3758, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3748, c_1901])).
% 4.35/1.84  tff(c_3769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1512, c_3758])).
% 4.35/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.84  
% 4.35/1.84  Inference rules
% 4.35/1.84  ----------------------
% 4.35/1.84  #Ref     : 0
% 4.35/1.84  #Sup     : 869
% 4.35/1.84  #Fact    : 0
% 4.35/1.84  #Define  : 0
% 4.35/1.84  #Split   : 8
% 4.35/1.84  #Chain   : 0
% 4.35/1.84  #Close   : 0
% 4.35/1.84  
% 4.35/1.84  Ordering : KBO
% 4.35/1.84  
% 4.35/1.84  Simplification rules
% 4.35/1.84  ----------------------
% 4.35/1.84  #Subsume      : 64
% 4.35/1.84  #Demod        : 650
% 4.35/1.84  #Tautology    : 615
% 4.35/1.84  #SimpNegUnit  : 5
% 4.35/1.84  #BackRed      : 6
% 4.35/1.84  
% 4.35/1.84  #Partial instantiations: 0
% 4.35/1.84  #Strategies tried      : 1
% 4.35/1.84  
% 4.35/1.84  Timing (in seconds)
% 4.35/1.84  ----------------------
% 4.35/1.84  Preprocessing        : 0.34
% 4.35/1.84  Parsing              : 0.19
% 4.35/1.84  CNF conversion       : 0.02
% 4.35/1.84  Main loop            : 0.66
% 4.35/1.84  Inferencing          : 0.22
% 4.35/1.84  Reduction            : 0.25
% 4.35/1.84  Demodulation         : 0.19
% 4.35/1.84  BG Simplification    : 0.03
% 4.35/1.84  Subsumption          : 0.11
% 4.35/1.84  Abstraction          : 0.03
% 4.35/1.84  MUC search           : 0.00
% 4.35/1.84  Cooper               : 0.00
% 4.35/1.84  Total                : 1.04
% 4.35/1.84  Index Insertion      : 0.00
% 4.35/1.84  Index Deletion       : 0.00
% 4.35/1.84  Index Matching       : 0.00
% 4.35/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
