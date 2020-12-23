%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:29 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 307 expanded)
%              Number of leaves         :   30 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  217 (1048 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_926,plain,(
    ! [B_108,A_109] :
      ( l1_pre_topc(B_108)
      | ~ m1_pre_topc(B_108,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_932,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_926])).

tff(c_939,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_932])).

tff(c_20,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_935,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_926])).

tff(c_942,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_935])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_81,plain,(
    ! [B_43,A_44] :
      ( l1_pre_topc(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_87,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_81])).

tff(c_94,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_87])).

tff(c_36,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_129,plain,(
    ! [B_49,A_50] :
      ( r1_tsep_1(B_49,A_50)
      | ~ r1_tsep_1(A_50,B_49)
      | ~ l1_struct_0(B_49)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_132,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_129])).

tff(c_135,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_138,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_135])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_138])).

tff(c_144,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_97,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_90])).

tff(c_143,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_145,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_148,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_145])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_148])).

tff(c_154,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_110,plain,(
    ! [B_47,A_48] :
      ( v2_pre_topc(B_47)
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_119,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_110])).

tff(c_128,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_119])).

tff(c_153,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_155,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(u1_struct_0(A_51),u1_struct_0(B_52))
      | ~ r1_tsep_1(A_51,B_52)
      | ~ l1_struct_0(B_52)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_159,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(u1_struct_0(A_51),u1_struct_0(B_52)) = u1_struct_0(A_51)
      | ~ r1_tsep_1(A_51,B_52)
      | ~ l1_struct_0(B_52)
      | ~ l1_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_155,c_14])).

tff(c_230,plain,(
    ! [B_65,C_66,A_67] :
      ( r1_tarski(u1_struct_0(B_65),u1_struct_0(C_66))
      | ~ m1_pre_topc(B_65,C_66)
      | ~ m1_pre_topc(C_66,A_67)
      | ~ m1_pre_topc(B_65,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_232,plain,(
    ! [B_65] :
      ( r1_tarski(u1_struct_0(B_65),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_65,'#skF_2')
      | ~ m1_pre_topc(B_65,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_230])).

tff(c_246,plain,(
    ! [B_68] :
      ( r1_tarski(u1_struct_0(B_68),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_68,'#skF_2')
      | ~ m1_pre_topc(B_68,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_97,c_232])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_324,plain,(
    ! [B_72] :
      ( k4_xboole_0(u1_struct_0(B_72),u1_struct_0('#skF_2')) = k1_xboole_0
      | ~ m1_pre_topc(B_72,'#skF_2')
      | ~ m1_pre_topc(B_72,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_246,c_12])).

tff(c_346,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k1_xboole_0
      | ~ m1_pre_topc(A_51,'#skF_2')
      | ~ m1_pre_topc(A_51,'#skF_3')
      | ~ r1_tsep_1(A_51,'#skF_2')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_324])).

tff(c_429,plain,(
    ! [A_75] :
      ( u1_struct_0(A_75) = k1_xboole_0
      | ~ m1_pre_topc(A_75,'#skF_2')
      | ~ m1_pre_topc(A_75,'#skF_3')
      | ~ r1_tsep_1(A_75,'#skF_2')
      | ~ l1_struct_0(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_346])).

tff(c_436,plain,
    ( u1_struct_0('#skF_3') = k1_xboole_0
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_429])).

tff(c_442,plain,
    ( u1_struct_0('#skF_3') = k1_xboole_0
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_436])).

tff(c_443,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_442])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_444,plain,(
    ! [B_76,C_77,A_78] :
      ( m1_pre_topc(B_76,C_77)
      | ~ r1_tarski(u1_struct_0(B_76),u1_struct_0(C_77))
      | ~ m1_pre_topc(C_77,A_78)
      | ~ m1_pre_topc(B_76,A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_462,plain,(
    ! [B_79,A_80] :
      ( m1_pre_topc(B_79,B_79)
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_8,c_444])).

tff(c_468,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_462])).

tff(c_477,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_468])).

tff(c_479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_443,c_477])).

tff(c_481,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_442])).

tff(c_32,plain,(
    ! [B_24,C_26,A_20] :
      ( r1_tarski(u1_struct_0(B_24),u1_struct_0(C_26))
      | ~ m1_pre_topc(B_24,C_26)
      | ~ m1_pre_topc(C_26,A_20)
      | ~ m1_pre_topc(B_24,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_483,plain,(
    ! [B_24] :
      ( r1_tarski(u1_struct_0(B_24),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_24,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_481,c_32])).

tff(c_535,plain,(
    ! [B_82] :
      ( r1_tarski(u1_struct_0(B_82),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_82,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_97,c_483])).

tff(c_573,plain,(
    ! [B_86] :
      ( k4_xboole_0(u1_struct_0(B_86),u1_struct_0('#skF_3')) = k1_xboole_0
      | ~ m1_pre_topc(B_86,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_535,c_12])).

tff(c_582,plain,(
    ! [B_86] :
      ( u1_struct_0(B_86) = k1_xboole_0
      | ~ r1_tsep_1(B_86,'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0(B_86)
      | ~ m1_pre_topc(B_86,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_159])).

tff(c_804,plain,(
    ! [B_97] :
      ( u1_struct_0(B_97) = k1_xboole_0
      | ~ r1_tsep_1(B_97,'#skF_3')
      | ~ l1_struct_0(B_97)
      | ~ m1_pre_topc(B_97,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_582])).

tff(c_818,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_804])).

tff(c_828,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_144,c_818])).

tff(c_24,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_871,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_24])).

tff(c_897,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_2,c_871])).

tff(c_899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_897])).

tff(c_901,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_900,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_973,plain,(
    ! [B_114,A_115] :
      ( r1_tsep_1(B_114,A_115)
      | ~ r1_tsep_1(A_115,B_114)
      | ~ l1_struct_0(B_114)
      | ~ l1_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_975,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_900,c_973])).

tff(c_978,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_901,c_975])).

tff(c_981,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_978])).

tff(c_984,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_981])).

tff(c_988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_984])).

tff(c_989,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_978])).

tff(c_993,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_989])).

tff(c_997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_993])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:14:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.51  
% 2.75/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.51  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.75/1.51  
% 2.75/1.51  %Foreground sorts:
% 2.75/1.51  
% 2.75/1.51  
% 2.75/1.51  %Background operators:
% 2.75/1.51  
% 2.75/1.51  
% 2.75/1.51  %Foreground operators:
% 2.75/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.75/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.75/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.75/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.75/1.51  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.75/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.51  
% 2.75/1.53  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.75/1.53  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.75/1.53  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.75/1.53  tff(f_85, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.75/1.53  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.75/1.53  tff(f_49, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.75/1.53  tff(f_77, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.75/1.53  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.75/1.53  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.75/1.53  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.75/1.53  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.75/1.53  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.75/1.53  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.75/1.53  tff(c_44, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.75/1.53  tff(c_926, plain, (![B_108, A_109]: (l1_pre_topc(B_108) | ~m1_pre_topc(B_108, A_109) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.75/1.53  tff(c_932, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_926])).
% 2.75/1.53  tff(c_939, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_932])).
% 2.75/1.53  tff(c_20, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.53  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.75/1.53  tff(c_935, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_926])).
% 2.75/1.53  tff(c_942, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_935])).
% 2.75/1.53  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.75/1.53  tff(c_81, plain, (![B_43, A_44]: (l1_pre_topc(B_43) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.75/1.53  tff(c_87, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_81])).
% 2.75/1.53  tff(c_94, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_87])).
% 2.75/1.53  tff(c_36, plain, (r1_tsep_1('#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.75/1.53  tff(c_56, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 2.75/1.53  tff(c_129, plain, (![B_49, A_50]: (r1_tsep_1(B_49, A_50) | ~r1_tsep_1(A_50, B_49) | ~l1_struct_0(B_49) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.75/1.53  tff(c_132, plain, (r1_tsep_1('#skF_3', '#skF_2') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_129])).
% 2.75/1.53  tff(c_135, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_132])).
% 2.75/1.53  tff(c_138, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_135])).
% 2.75/1.53  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_138])).
% 2.75/1.53  tff(c_144, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_132])).
% 2.75/1.53  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.75/1.53  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.75/1.53  tff(c_90, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_81])).
% 2.75/1.53  tff(c_97, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_90])).
% 2.75/1.53  tff(c_143, plain, (~l1_struct_0('#skF_3') | r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_132])).
% 2.75/1.53  tff(c_145, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_143])).
% 2.75/1.53  tff(c_148, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_145])).
% 2.75/1.53  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_148])).
% 2.75/1.53  tff(c_154, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_143])).
% 2.75/1.53  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.75/1.53  tff(c_110, plain, (![B_47, A_48]: (v2_pre_topc(B_47) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.53  tff(c_119, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_110])).
% 2.75/1.53  tff(c_128, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_119])).
% 2.75/1.53  tff(c_153, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_143])).
% 2.75/1.53  tff(c_155, plain, (![A_51, B_52]: (r1_xboole_0(u1_struct_0(A_51), u1_struct_0(B_52)) | ~r1_tsep_1(A_51, B_52) | ~l1_struct_0(B_52) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.75/1.53  tff(c_14, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.53  tff(c_159, plain, (![A_51, B_52]: (k4_xboole_0(u1_struct_0(A_51), u1_struct_0(B_52))=u1_struct_0(A_51) | ~r1_tsep_1(A_51, B_52) | ~l1_struct_0(B_52) | ~l1_struct_0(A_51))), inference(resolution, [status(thm)], [c_155, c_14])).
% 2.75/1.53  tff(c_230, plain, (![B_65, C_66, A_67]: (r1_tarski(u1_struct_0(B_65), u1_struct_0(C_66)) | ~m1_pre_topc(B_65, C_66) | ~m1_pre_topc(C_66, A_67) | ~m1_pre_topc(B_65, A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.75/1.53  tff(c_232, plain, (![B_65]: (r1_tarski(u1_struct_0(B_65), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_65, '#skF_2') | ~m1_pre_topc(B_65, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_230])).
% 2.75/1.53  tff(c_246, plain, (![B_68]: (r1_tarski(u1_struct_0(B_68), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_68, '#skF_2') | ~m1_pre_topc(B_68, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_97, c_232])).
% 2.75/1.53  tff(c_12, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.75/1.53  tff(c_324, plain, (![B_72]: (k4_xboole_0(u1_struct_0(B_72), u1_struct_0('#skF_2'))=k1_xboole_0 | ~m1_pre_topc(B_72, '#skF_2') | ~m1_pre_topc(B_72, '#skF_3'))), inference(resolution, [status(thm)], [c_246, c_12])).
% 2.75/1.53  tff(c_346, plain, (![A_51]: (u1_struct_0(A_51)=k1_xboole_0 | ~m1_pre_topc(A_51, '#skF_2') | ~m1_pre_topc(A_51, '#skF_3') | ~r1_tsep_1(A_51, '#skF_2') | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_51))), inference(superposition, [status(thm), theory('equality')], [c_159, c_324])).
% 2.75/1.53  tff(c_429, plain, (![A_75]: (u1_struct_0(A_75)=k1_xboole_0 | ~m1_pre_topc(A_75, '#skF_2') | ~m1_pre_topc(A_75, '#skF_3') | ~r1_tsep_1(A_75, '#skF_2') | ~l1_struct_0(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_346])).
% 2.75/1.53  tff(c_436, plain, (u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_153, c_429])).
% 2.75/1.53  tff(c_442, plain, (u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_436])).
% 2.75/1.53  tff(c_443, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_442])).
% 2.75/1.53  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.53  tff(c_444, plain, (![B_76, C_77, A_78]: (m1_pre_topc(B_76, C_77) | ~r1_tarski(u1_struct_0(B_76), u1_struct_0(C_77)) | ~m1_pre_topc(C_77, A_78) | ~m1_pre_topc(B_76, A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.75/1.53  tff(c_462, plain, (![B_79, A_80]: (m1_pre_topc(B_79, B_79) | ~m1_pre_topc(B_79, A_80) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(resolution, [status(thm)], [c_8, c_444])).
% 2.75/1.53  tff(c_468, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_462])).
% 2.75/1.53  tff(c_477, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_468])).
% 2.75/1.53  tff(c_479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_443, c_477])).
% 2.75/1.53  tff(c_481, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_442])).
% 2.75/1.53  tff(c_32, plain, (![B_24, C_26, A_20]: (r1_tarski(u1_struct_0(B_24), u1_struct_0(C_26)) | ~m1_pre_topc(B_24, C_26) | ~m1_pre_topc(C_26, A_20) | ~m1_pre_topc(B_24, A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.75/1.53  tff(c_483, plain, (![B_24]: (r1_tarski(u1_struct_0(B_24), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_24, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_481, c_32])).
% 2.75/1.53  tff(c_535, plain, (![B_82]: (r1_tarski(u1_struct_0(B_82), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_82, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_97, c_483])).
% 2.75/1.53  tff(c_573, plain, (![B_86]: (k4_xboole_0(u1_struct_0(B_86), u1_struct_0('#skF_3'))=k1_xboole_0 | ~m1_pre_topc(B_86, '#skF_3'))), inference(resolution, [status(thm)], [c_535, c_12])).
% 2.75/1.53  tff(c_582, plain, (![B_86]: (u1_struct_0(B_86)=k1_xboole_0 | ~r1_tsep_1(B_86, '#skF_3') | ~l1_struct_0('#skF_3') | ~l1_struct_0(B_86) | ~m1_pre_topc(B_86, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_573, c_159])).
% 2.75/1.53  tff(c_804, plain, (![B_97]: (u1_struct_0(B_97)=k1_xboole_0 | ~r1_tsep_1(B_97, '#skF_3') | ~l1_struct_0(B_97) | ~m1_pre_topc(B_97, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_582])).
% 2.75/1.53  tff(c_818, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | ~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_804])).
% 2.75/1.53  tff(c_828, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_144, c_818])).
% 2.75/1.53  tff(c_24, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.75/1.53  tff(c_871, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_828, c_24])).
% 2.75/1.53  tff(c_897, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_2, c_871])).
% 2.75/1.53  tff(c_899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_897])).
% 2.75/1.53  tff(c_901, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.75/1.53  tff(c_900, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 2.75/1.53  tff(c_973, plain, (![B_114, A_115]: (r1_tsep_1(B_114, A_115) | ~r1_tsep_1(A_115, B_114) | ~l1_struct_0(B_114) | ~l1_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.75/1.53  tff(c_975, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_900, c_973])).
% 2.75/1.53  tff(c_978, plain, (~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_901, c_975])).
% 2.75/1.53  tff(c_981, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_978])).
% 2.75/1.53  tff(c_984, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_981])).
% 2.75/1.53  tff(c_988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_942, c_984])).
% 2.75/1.53  tff(c_989, plain, (~l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_978])).
% 2.75/1.53  tff(c_993, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_989])).
% 2.75/1.53  tff(c_997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_939, c_993])).
% 2.75/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.53  
% 2.75/1.53  Inference rules
% 2.75/1.53  ----------------------
% 2.75/1.53  #Ref     : 0
% 2.75/1.53  #Sup     : 178
% 2.75/1.53  #Fact    : 0
% 2.75/1.53  #Define  : 0
% 2.75/1.53  #Split   : 6
% 2.75/1.53  #Chain   : 0
% 2.75/1.53  #Close   : 0
% 2.75/1.53  
% 2.75/1.53  Ordering : KBO
% 2.75/1.53  
% 2.75/1.53  Simplification rules
% 2.75/1.53  ----------------------
% 2.75/1.53  #Subsume      : 16
% 2.75/1.53  #Demod        : 165
% 2.75/1.53  #Tautology    : 76
% 2.75/1.53  #SimpNegUnit  : 3
% 2.75/1.53  #BackRed      : 2
% 2.75/1.53  
% 2.75/1.53  #Partial instantiations: 0
% 2.75/1.53  #Strategies tried      : 1
% 2.75/1.53  
% 2.75/1.53  Timing (in seconds)
% 2.75/1.53  ----------------------
% 2.75/1.53  Preprocessing        : 0.29
% 2.75/1.53  Parsing              : 0.16
% 2.75/1.53  CNF conversion       : 0.02
% 2.75/1.53  Main loop            : 0.36
% 2.75/1.53  Inferencing          : 0.13
% 2.75/1.53  Reduction            : 0.10
% 2.75/1.53  Demodulation         : 0.07
% 2.75/1.53  BG Simplification    : 0.02
% 2.75/1.53  Subsumption          : 0.07
% 2.75/1.53  Abstraction          : 0.01
% 2.75/1.53  MUC search           : 0.00
% 2.75/1.53  Cooper               : 0.00
% 2.75/1.53  Total                : 0.69
% 2.75/1.53  Index Insertion      : 0.00
% 2.75/1.53  Index Deletion       : 0.00
% 2.75/1.53  Index Matching       : 0.00
% 2.75/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
