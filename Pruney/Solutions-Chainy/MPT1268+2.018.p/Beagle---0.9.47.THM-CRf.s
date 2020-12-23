%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:48 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 135 expanded)
%              Number of leaves         :   30 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 387 expanded)
%              Number of equality atoms :   23 (  55 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_108,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_59,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_197,plain,(
    ! [B_69,A_70] :
      ( v2_tops_1(B_69,A_70)
      | k1_tops_1(A_70,B_69) != k1_xboole_0
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_204,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_197])).

tff(c_208,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_204])).

tff(c_209,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_208])).

tff(c_138,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tops_1(A_64,B_65),B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_143,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_147,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_143])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_310,plain,(
    ! [A_80,B_81] :
      ( v3_pre_topc(k1_tops_1(A_80,B_81),A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_315,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_310])).

tff(c_319,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_315])).

tff(c_63,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_97,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(A_54,C_55)
      | ~ r1_tarski(B_56,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_54,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_71,c_97])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [C_37] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_37
      | ~ v3_pre_topc(C_37,'#skF_1')
      | ~ r1_tarski(C_37,'#skF_2')
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_230,plain,(
    ! [C_74] :
      ( k1_xboole_0 = C_74
      | ~ v3_pre_topc(C_74,'#skF_1')
      | ~ r1_tarski(C_74,'#skF_2')
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_56])).

tff(c_497,plain,(
    ! [A_94] :
      ( k1_xboole_0 = A_94
      | ~ v3_pre_topc(A_94,'#skF_1')
      | ~ r1_tarski(A_94,'#skF_2')
      | ~ r1_tarski(A_94,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_230])).

tff(c_550,plain,(
    ! [A_97] :
      ( k1_xboole_0 = A_97
      | ~ v3_pre_topc(A_97,'#skF_1')
      | ~ r1_tarski(A_97,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_104,c_497])).

tff(c_553,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_319,c_550])).

tff(c_556,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_553])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_556])).

tff(c_559,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_560,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_44,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_568,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_44])).

tff(c_569,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(A_102,B_103)
      | ~ m1_subset_1(A_102,k1_zfmisc_1(B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_576,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_568,c_569])).

tff(c_588,plain,(
    ! [A_108,C_109,B_110] :
      ( r1_xboole_0(A_108,k4_xboole_0(C_109,B_110))
      | ~ r1_tarski(A_108,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_856,plain,(
    ! [A_140,C_141,B_142] :
      ( k3_xboole_0(A_140,k4_xboole_0(C_141,B_142)) = k1_xboole_0
      | ~ r1_tarski(A_140,B_142) ) ),
    inference(resolution,[status(thm)],[c_588,c_2])).

tff(c_12,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_901,plain,(
    ! [A_143,B_144] :
      ( r1_tarski(k1_xboole_0,A_143)
      | ~ r1_tarski(A_143,B_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_12])).

tff(c_942,plain,(
    r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_576,c_901])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_966,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_942,c_6])).

tff(c_972,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_966])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_565,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_40])).

tff(c_42,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_563,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_42])).

tff(c_725,plain,(
    ! [A_128,B_129] :
      ( k1_tops_1(A_128,B_129) = k1_xboole_0
      | ~ v2_tops_1(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_735,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_725])).

tff(c_742,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_560,c_735])).

tff(c_1011,plain,(
    ! [B_148,A_149,C_150] :
      ( r1_tarski(B_148,k1_tops_1(A_149,C_150))
      | ~ r1_tarski(B_148,C_150)
      | ~ v3_pre_topc(B_148,A_149)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1018,plain,(
    ! [B_148] :
      ( r1_tarski(B_148,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_148,'#skF_2')
      | ~ v3_pre_topc(B_148,'#skF_1')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_1011])).

tff(c_1087,plain,(
    ! [B_153] :
      ( r1_tarski(B_153,k1_xboole_0)
      | ~ r1_tarski(B_153,'#skF_2')
      | ~ v3_pre_topc(B_153,'#skF_1')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_742,c_1018])).

tff(c_1094,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_568,c_1087])).

tff(c_1101,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_563,c_1094])).

tff(c_1103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_972,c_1101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:25:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.47  
% 3.08/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.47  %$ v3_pre_topc > v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.08/1.47  
% 3.08/1.47  %Foreground sorts:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Background operators:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Foreground operators:
% 3.08/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.08/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.47  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.08/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.08/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.08/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.08/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.08/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.08/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.08/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.47  
% 3.08/1.49  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.08/1.49  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.08/1.49  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.08/1.49  tff(f_59, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.08/1.49  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.08/1.49  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.08/1.49  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.08/1.49  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.08/1.49  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.08/1.49  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.08/1.49  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.08/1.49  tff(c_38, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.49  tff(c_59, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 3.08/1.49  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.49  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.49  tff(c_197, plain, (![B_69, A_70]: (v2_tops_1(B_69, A_70) | k1_tops_1(A_70, B_69)!=k1_xboole_0 | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.08/1.49  tff(c_204, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_197])).
% 3.08/1.49  tff(c_208, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_204])).
% 3.08/1.49  tff(c_209, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_59, c_208])).
% 3.08/1.49  tff(c_138, plain, (![A_64, B_65]: (r1_tarski(k1_tops_1(A_64, B_65), B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.08/1.49  tff(c_143, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_138])).
% 3.08/1.49  tff(c_147, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_143])).
% 3.08/1.49  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.49  tff(c_310, plain, (![A_80, B_81]: (v3_pre_topc(k1_tops_1(A_80, B_81), A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.49  tff(c_315, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_310])).
% 3.08/1.49  tff(c_319, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_315])).
% 3.08/1.49  tff(c_63, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.49  tff(c_71, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_63])).
% 3.08/1.49  tff(c_97, plain, (![A_54, C_55, B_56]: (r1_tarski(A_54, C_55) | ~r1_tarski(B_56, C_55) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.49  tff(c_104, plain, (![A_54]: (r1_tarski(A_54, u1_struct_0('#skF_1')) | ~r1_tarski(A_54, '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_97])).
% 3.08/1.49  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.49  tff(c_56, plain, (![C_37]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_37 | ~v3_pre_topc(C_37, '#skF_1') | ~r1_tarski(C_37, '#skF_2') | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.49  tff(c_230, plain, (![C_74]: (k1_xboole_0=C_74 | ~v3_pre_topc(C_74, '#skF_1') | ~r1_tarski(C_74, '#skF_2') | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_59, c_56])).
% 3.08/1.49  tff(c_497, plain, (![A_94]: (k1_xboole_0=A_94 | ~v3_pre_topc(A_94, '#skF_1') | ~r1_tarski(A_94, '#skF_2') | ~r1_tarski(A_94, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_230])).
% 3.08/1.49  tff(c_550, plain, (![A_97]: (k1_xboole_0=A_97 | ~v3_pre_topc(A_97, '#skF_1') | ~r1_tarski(A_97, '#skF_2'))), inference(resolution, [status(thm)], [c_104, c_497])).
% 3.08/1.49  tff(c_553, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_319, c_550])).
% 3.08/1.49  tff(c_556, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_147, c_553])).
% 3.08/1.49  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_556])).
% 3.08/1.49  tff(c_559, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 3.08/1.49  tff(c_560, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 3.08/1.49  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.49  tff(c_568, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_44])).
% 3.08/1.49  tff(c_569, plain, (![A_102, B_103]: (r1_tarski(A_102, B_103) | ~m1_subset_1(A_102, k1_zfmisc_1(B_103)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.49  tff(c_576, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_568, c_569])).
% 3.08/1.49  tff(c_588, plain, (![A_108, C_109, B_110]: (r1_xboole_0(A_108, k4_xboole_0(C_109, B_110)) | ~r1_tarski(A_108, B_110))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.08/1.49  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.49  tff(c_856, plain, (![A_140, C_141, B_142]: (k3_xboole_0(A_140, k4_xboole_0(C_141, B_142))=k1_xboole_0 | ~r1_tarski(A_140, B_142))), inference(resolution, [status(thm)], [c_588, c_2])).
% 3.08/1.49  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.49  tff(c_901, plain, (![A_143, B_144]: (r1_tarski(k1_xboole_0, A_143) | ~r1_tarski(A_143, B_144))), inference(superposition, [status(thm), theory('equality')], [c_856, c_12])).
% 3.08/1.49  tff(c_942, plain, (r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_576, c_901])).
% 3.08/1.49  tff(c_6, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.08/1.49  tff(c_966, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_942, c_6])).
% 3.08/1.49  tff(c_972, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_559, c_966])).
% 3.08/1.49  tff(c_40, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.49  tff(c_565, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_560, c_40])).
% 3.08/1.49  tff(c_42, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.49  tff(c_563, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_560, c_42])).
% 3.08/1.49  tff(c_725, plain, (![A_128, B_129]: (k1_tops_1(A_128, B_129)=k1_xboole_0 | ~v2_tops_1(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.08/1.49  tff(c_735, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_725])).
% 3.08/1.49  tff(c_742, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_560, c_735])).
% 3.08/1.49  tff(c_1011, plain, (![B_148, A_149, C_150]: (r1_tarski(B_148, k1_tops_1(A_149, C_150)) | ~r1_tarski(B_148, C_150) | ~v3_pre_topc(B_148, A_149) | ~m1_subset_1(C_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.08/1.49  tff(c_1018, plain, (![B_148]: (r1_tarski(B_148, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_148, '#skF_2') | ~v3_pre_topc(B_148, '#skF_1') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_1011])).
% 3.08/1.49  tff(c_1087, plain, (![B_153]: (r1_tarski(B_153, k1_xboole_0) | ~r1_tarski(B_153, '#skF_2') | ~v3_pre_topc(B_153, '#skF_1') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_742, c_1018])).
% 3.08/1.49  tff(c_1094, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_568, c_1087])).
% 3.08/1.49  tff(c_1101, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_565, c_563, c_1094])).
% 3.08/1.49  tff(c_1103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_972, c_1101])).
% 3.08/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.49  
% 3.08/1.49  Inference rules
% 3.08/1.49  ----------------------
% 3.08/1.49  #Ref     : 0
% 3.08/1.49  #Sup     : 226
% 3.08/1.49  #Fact    : 0
% 3.08/1.49  #Define  : 0
% 3.08/1.49  #Split   : 12
% 3.08/1.49  #Chain   : 0
% 3.08/1.49  #Close   : 0
% 3.08/1.49  
% 3.08/1.49  Ordering : KBO
% 3.08/1.49  
% 3.08/1.49  Simplification rules
% 3.08/1.49  ----------------------
% 3.08/1.49  #Subsume      : 40
% 3.08/1.49  #Demod        : 115
% 3.08/1.49  #Tautology    : 89
% 3.08/1.49  #SimpNegUnit  : 7
% 3.08/1.49  #BackRed      : 4
% 3.08/1.49  
% 3.08/1.49  #Partial instantiations: 0
% 3.08/1.49  #Strategies tried      : 1
% 3.08/1.49  
% 3.08/1.49  Timing (in seconds)
% 3.08/1.49  ----------------------
% 3.08/1.49  Preprocessing        : 0.31
% 3.08/1.49  Parsing              : 0.16
% 3.08/1.49  CNF conversion       : 0.02
% 3.08/1.49  Main loop            : 0.39
% 3.08/1.49  Inferencing          : 0.13
% 3.08/1.49  Reduction            : 0.12
% 3.08/1.49  Demodulation         : 0.08
% 3.08/1.49  BG Simplification    : 0.02
% 3.08/1.49  Subsumption          : 0.08
% 3.08/1.49  Abstraction          : 0.02
% 3.08/1.49  MUC search           : 0.00
% 3.08/1.49  Cooper               : 0.00
% 3.08/1.49  Total                : 0.74
% 3.08/1.49  Index Insertion      : 0.00
% 3.08/1.49  Index Deletion       : 0.00
% 3.08/1.49  Index Matching       : 0.00
% 3.08/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
