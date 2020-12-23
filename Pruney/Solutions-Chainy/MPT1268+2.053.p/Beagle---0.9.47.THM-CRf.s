%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:54 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 130 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 382 expanded)
%              Number of equality atoms :   27 (  61 expanded)
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

tff(f_98,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_49,axiom,(
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

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_70,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_58,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_479,plain,(
    ! [B_77,A_78] :
      ( v2_tops_1(B_77,A_78)
      | k1_tops_1(A_78,B_77) != k1_xboole_0
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_486,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_479])).

tff(c_490,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_486])).

tff(c_491,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_490])).

tff(c_61,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_4])).

tff(c_149,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_tops_1(A_52,B_53),B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_154,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_149])).

tff(c_158,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_154])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_325,plain,(
    ! [A_67,B_68] :
      ( v3_pre_topc(k1_tops_1(A_67,B_68),A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_330,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_325])).

tff(c_334,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_330])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,C_42)
      | ~ r1_tarski(B_43,C_42)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    ! [A_41,B_2,A_1] :
      ( r1_tarski(A_41,B_2)
      | ~ r1_tarski(A_41,A_1)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_83])).

tff(c_169,plain,(
    ! [B_2] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_2)
      | k4_xboole_0('#skF_2',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_158,c_88])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [C_31] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_31
      | ~ v3_pre_topc(C_31,'#skF_1')
      | ~ r1_tarski(C_31,'#skF_2')
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_183,plain,(
    ! [C_55] :
      ( k1_xboole_0 = C_55
      | ~ v3_pre_topc(C_55,'#skF_1')
      | ~ r1_tarski(C_55,'#skF_2')
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_48])).

tff(c_620,plain,(
    ! [A_92] :
      ( k1_xboole_0 = A_92
      | ~ v3_pre_topc(A_92,'#skF_1')
      | ~ r1_tarski(A_92,'#skF_2')
      | ~ r1_tarski(A_92,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_183])).

tff(c_638,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_169,c_620])).

tff(c_655,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_158,c_334,c_638])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_655])).

tff(c_658,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_659,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_663,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_32])).

tff(c_34,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_661,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_34])).

tff(c_36,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_680,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_36])).

tff(c_934,plain,(
    ! [A_115,B_116] :
      ( k1_tops_1(A_115,B_116) = k1_xboole_0
      | ~ v2_tops_1(B_116,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_944,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_934])).

tff(c_951,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_659,c_944])).

tff(c_1153,plain,(
    ! [B_130,A_131,C_132] :
      ( r1_tarski(B_130,k1_tops_1(A_131,C_132))
      | ~ r1_tarski(B_130,C_132)
      | ~ v3_pre_topc(B_130,A_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1160,plain,(
    ! [B_130] :
      ( r1_tarski(B_130,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_130,'#skF_2')
      | ~ v3_pre_topc(B_130,'#skF_1')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_1153])).

tff(c_1507,plain,(
    ! [B_148] :
      ( r1_tarski(B_148,k1_xboole_0)
      | ~ r1_tarski(B_148,'#skF_2')
      | ~ v3_pre_topc(B_148,'#skF_1')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_951,c_1160])).

tff(c_1510,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_680,c_1507])).

tff(c_1520,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_661,c_1510])).

tff(c_1536,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1520,c_4])).

tff(c_1546,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1536])).

tff(c_1548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_1546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.71  
% 3.34/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.71  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.34/1.71  
% 3.34/1.71  %Foreground sorts:
% 3.34/1.71  
% 3.34/1.71  
% 3.34/1.71  %Background operators:
% 3.34/1.71  
% 3.34/1.71  
% 3.34/1.71  %Foreground operators:
% 3.34/1.71  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.34/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.71  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.34/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.34/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.71  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.34/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.34/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.34/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.71  
% 3.70/1.73  tff(f_98, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.70/1.73  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.70/1.73  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.70/1.73  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.70/1.73  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.70/1.73  tff(f_49, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.70/1.73  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.70/1.73  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.70/1.73  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.70/1.73  tff(c_30, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.70/1.73  tff(c_58, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.70/1.73  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.70/1.73  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.70/1.73  tff(c_479, plain, (![B_77, A_78]: (v2_tops_1(B_77, A_78) | k1_tops_1(A_78, B_77)!=k1_xboole_0 | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.70/1.73  tff(c_486, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_479])).
% 3.70/1.73  tff(c_490, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_486])).
% 3.70/1.73  tff(c_491, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_490])).
% 3.70/1.73  tff(c_61, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.70/1.73  tff(c_69, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_61])).
% 3.70/1.73  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.70/1.73  tff(c_73, plain, (k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_4])).
% 3.70/1.73  tff(c_149, plain, (![A_52, B_53]: (r1_tarski(k1_tops_1(A_52, B_53), B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.70/1.73  tff(c_154, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_149])).
% 3.70/1.73  tff(c_158, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_154])).
% 3.70/1.73  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.70/1.73  tff(c_325, plain, (![A_67, B_68]: (v3_pre_topc(k1_tops_1(A_67, B_68), A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.70/1.73  tff(c_330, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_325])).
% 3.70/1.73  tff(c_334, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_330])).
% 3.70/1.73  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.70/1.73  tff(c_83, plain, (![A_41, C_42, B_43]: (r1_tarski(A_41, C_42) | ~r1_tarski(B_43, C_42) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.70/1.73  tff(c_88, plain, (![A_41, B_2, A_1]: (r1_tarski(A_41, B_2) | ~r1_tarski(A_41, A_1) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_83])).
% 3.70/1.73  tff(c_169, plain, (![B_2]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_2) | k4_xboole_0('#skF_2', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_158, c_88])).
% 3.70/1.73  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.70/1.73  tff(c_48, plain, (![C_31]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_31 | ~v3_pre_topc(C_31, '#skF_1') | ~r1_tarski(C_31, '#skF_2') | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.70/1.73  tff(c_183, plain, (![C_55]: (k1_xboole_0=C_55 | ~v3_pre_topc(C_55, '#skF_1') | ~r1_tarski(C_55, '#skF_2') | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_48])).
% 3.70/1.73  tff(c_620, plain, (![A_92]: (k1_xboole_0=A_92 | ~v3_pre_topc(A_92, '#skF_1') | ~r1_tarski(A_92, '#skF_2') | ~r1_tarski(A_92, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_183])).
% 3.70/1.73  tff(c_638, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_169, c_620])).
% 3.70/1.73  tff(c_655, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_73, c_158, c_334, c_638])).
% 3.70/1.73  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_655])).
% 3.70/1.73  tff(c_658, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 3.70/1.73  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.70/1.73  tff(c_659, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.70/1.73  tff(c_32, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.70/1.73  tff(c_663, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_659, c_32])).
% 3.70/1.73  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.70/1.73  tff(c_661, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_659, c_34])).
% 3.70/1.73  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.70/1.73  tff(c_680, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_36])).
% 3.70/1.73  tff(c_934, plain, (![A_115, B_116]: (k1_tops_1(A_115, B_116)=k1_xboole_0 | ~v2_tops_1(B_116, A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.70/1.73  tff(c_944, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_934])).
% 3.70/1.73  tff(c_951, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_659, c_944])).
% 3.70/1.73  tff(c_1153, plain, (![B_130, A_131, C_132]: (r1_tarski(B_130, k1_tops_1(A_131, C_132)) | ~r1_tarski(B_130, C_132) | ~v3_pre_topc(B_130, A_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.70/1.73  tff(c_1160, plain, (![B_130]: (r1_tarski(B_130, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_130, '#skF_2') | ~v3_pre_topc(B_130, '#skF_1') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1153])).
% 3.70/1.73  tff(c_1507, plain, (![B_148]: (r1_tarski(B_148, k1_xboole_0) | ~r1_tarski(B_148, '#skF_2') | ~v3_pre_topc(B_148, '#skF_1') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_951, c_1160])).
% 3.70/1.73  tff(c_1510, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_680, c_1507])).
% 3.70/1.73  tff(c_1520, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_663, c_661, c_1510])).
% 3.70/1.73  tff(c_1536, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1520, c_4])).
% 3.70/1.73  tff(c_1546, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1536])).
% 3.70/1.73  tff(c_1548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_658, c_1546])).
% 3.70/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.73  
% 3.70/1.73  Inference rules
% 3.70/1.73  ----------------------
% 3.70/1.73  #Ref     : 0
% 3.70/1.73  #Sup     : 356
% 3.70/1.73  #Fact    : 0
% 3.70/1.73  #Define  : 0
% 3.70/1.73  #Split   : 12
% 3.70/1.73  #Chain   : 0
% 3.70/1.73  #Close   : 0
% 3.70/1.73  
% 3.70/1.73  Ordering : KBO
% 3.70/1.73  
% 3.70/1.73  Simplification rules
% 3.70/1.73  ----------------------
% 3.70/1.73  #Subsume      : 95
% 3.70/1.73  #Demod        : 103
% 3.70/1.73  #Tautology    : 110
% 3.70/1.73  #SimpNegUnit  : 7
% 3.70/1.73  #BackRed      : 2
% 3.70/1.73  
% 3.70/1.73  #Partial instantiations: 0
% 3.70/1.73  #Strategies tried      : 1
% 3.70/1.73  
% 3.70/1.73  Timing (in seconds)
% 3.70/1.73  ----------------------
% 3.70/1.73  Preprocessing        : 0.33
% 3.70/1.73  Parsing              : 0.17
% 3.70/1.73  CNF conversion       : 0.02
% 3.70/1.73  Main loop            : 0.49
% 3.70/1.73  Inferencing          : 0.16
% 3.70/1.73  Reduction            : 0.15
% 3.70/1.73  Demodulation         : 0.10
% 3.70/1.73  BG Simplification    : 0.02
% 3.70/1.73  Subsumption          : 0.12
% 3.70/1.73  Abstraction          : 0.02
% 3.70/1.73  MUC search           : 0.00
% 3.70/1.73  Cooper               : 0.00
% 3.70/1.73  Total                : 0.85
% 3.70/1.73  Index Insertion      : 0.00
% 3.70/1.73  Index Deletion       : 0.00
% 3.70/1.73  Index Matching       : 0.00
% 3.70/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
