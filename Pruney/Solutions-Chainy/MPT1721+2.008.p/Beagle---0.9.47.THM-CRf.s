%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:44 EST 2020

% Result     : Theorem 15.27s
% Output     : CNFRefutation 15.27s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 221 expanded)
%              Number of leaves         :   23 (  93 expanded)
%              Depth                    :   21
%              Number of atoms          :  272 (1358 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_135,negated_conjecture,(
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
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ( m1_pre_topc(B,D)
                        & m1_pre_topc(C,D) )
                     => ( r1_tsep_1(B,C)
                        | m1_pre_topc(k2_tsep_1(A,B,C),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_pre_topc(D)
                      & m1_pre_topc(D,A) )
                   => ( D = k2_tsep_1(A,B,C)
                    <=> u1_struct_0(D) = k3_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_101,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_12,plain,(
    ! [A_21,B_22,C_23] :
      ( v1_pre_topc(k2_tsep_1(A_21,B_22,C_23))
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10,plain,(
    ! [A_21,B_22,C_23] :
      ( m1_pre_topc(k2_tsep_1(A_21,B_22,C_23),A_21)
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_766,plain,(
    ! [A_142,B_143,C_144] :
      ( u1_struct_0(k2_tsep_1(A_142,B_143,C_144)) = k3_xboole_0(u1_struct_0(B_143),u1_struct_0(C_144))
      | ~ m1_pre_topc(k2_tsep_1(A_142,B_143,C_144),A_142)
      | ~ v1_pre_topc(k2_tsep_1(A_142,B_143,C_144))
      | v2_struct_0(k2_tsep_1(A_142,B_143,C_144))
      | r1_tsep_1(B_143,C_144)
      | ~ m1_pre_topc(C_144,A_142)
      | v2_struct_0(C_144)
      | ~ m1_pre_topc(B_143,A_142)
      | v2_struct_0(B_143)
      | ~ l1_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1021,plain,(
    ! [A_176,B_177,C_178] :
      ( u1_struct_0(k2_tsep_1(A_176,B_177,C_178)) = k3_xboole_0(u1_struct_0(B_177),u1_struct_0(C_178))
      | ~ v1_pre_topc(k2_tsep_1(A_176,B_177,C_178))
      | v2_struct_0(k2_tsep_1(A_176,B_177,C_178))
      | r1_tsep_1(B_177,C_178)
      | ~ m1_pre_topc(C_178,A_176)
      | v2_struct_0(C_178)
      | ~ m1_pre_topc(B_177,A_176)
      | v2_struct_0(B_177)
      | ~ l1_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_10,c_766])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1490,plain,(
    ! [A_215,B_216,C_217] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_215,B_216,C_217)),u1_struct_0(B_216))
      | ~ v1_pre_topc(k2_tsep_1(A_215,B_216,C_217))
      | v2_struct_0(k2_tsep_1(A_215,B_216,C_217))
      | r1_tsep_1(B_216,C_217)
      | ~ m1_pre_topc(C_217,A_215)
      | v2_struct_0(C_217)
      | ~ m1_pre_topc(B_216,A_215)
      | v2_struct_0(B_216)
      | ~ l1_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_2])).

tff(c_18,plain,(
    ! [B_28,C_30,A_24] :
      ( m1_pre_topc(B_28,C_30)
      | ~ r1_tarski(u1_struct_0(B_28),u1_struct_0(C_30))
      | ~ m1_pre_topc(C_30,A_24)
      | ~ m1_pre_topc(B_28,A_24)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10220,plain,(
    ! [A_1030,B_1031,C_1032,A_1033] :
      ( m1_pre_topc(k2_tsep_1(A_1030,B_1031,C_1032),B_1031)
      | ~ m1_pre_topc(B_1031,A_1033)
      | ~ m1_pre_topc(k2_tsep_1(A_1030,B_1031,C_1032),A_1033)
      | ~ l1_pre_topc(A_1033)
      | ~ v2_pre_topc(A_1033)
      | ~ v1_pre_topc(k2_tsep_1(A_1030,B_1031,C_1032))
      | v2_struct_0(k2_tsep_1(A_1030,B_1031,C_1032))
      | r1_tsep_1(B_1031,C_1032)
      | ~ m1_pre_topc(C_1032,A_1030)
      | v2_struct_0(C_1032)
      | ~ m1_pre_topc(B_1031,A_1030)
      | v2_struct_0(B_1031)
      | ~ l1_pre_topc(A_1030)
      | v2_struct_0(A_1030) ) ),
    inference(resolution,[status(thm)],[c_1490,c_18])).

tff(c_15931,plain,(
    ! [A_1703,B_1704,C_1705] :
      ( m1_pre_topc(k2_tsep_1(A_1703,B_1704,C_1705),B_1704)
      | ~ v2_pre_topc(A_1703)
      | ~ v1_pre_topc(k2_tsep_1(A_1703,B_1704,C_1705))
      | v2_struct_0(k2_tsep_1(A_1703,B_1704,C_1705))
      | r1_tsep_1(B_1704,C_1705)
      | ~ m1_pre_topc(C_1705,A_1703)
      | v2_struct_0(C_1705)
      | ~ m1_pre_topc(B_1704,A_1703)
      | v2_struct_0(B_1704)
      | ~ l1_pre_topc(A_1703)
      | v2_struct_0(A_1703) ) ),
    inference(resolution,[status(thm)],[c_10,c_10220])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_26,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_75,plain,(
    ! [B_60,C_61,A_62] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0(C_61))
      | ~ m1_pre_topc(B_60,C_61)
      | ~ m1_pre_topc(C_61,A_62)
      | ~ m1_pre_topc(B_60,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_81,plain,(
    ! [B_60] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_60,'#skF_2')
      | ~ m1_pre_topc(B_60,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_90,plain,(
    ! [B_60] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_60,'#skF_2')
      | ~ m1_pre_topc(B_60,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81])).

tff(c_83,plain,(
    ! [B_60] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_60,'#skF_4')
      | ~ m1_pre_topc(B_60,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_75])).

tff(c_121,plain,(
    ! [B_68] :
      ( r1_tarski(u1_struct_0(B_68),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_68,'#skF_4')
      | ~ m1_pre_topc(B_68,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_83])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_296,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(A_100,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_100,u1_struct_0(B_101))
      | ~ m1_pre_topc(B_101,'#skF_4')
      | ~ m1_pre_topc(B_101,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_121,c_4])).

tff(c_312,plain,(
    ! [B_60] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_2','#skF_4')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ m1_pre_topc(B_60,'#skF_2')
      | ~ m1_pre_topc(B_60,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_296])).

tff(c_364,plain,(
    ! [B_103] :
      ( r1_tarski(u1_struct_0(B_103),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_103,'#skF_2')
      | ~ m1_pre_topc(B_103,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_312])).

tff(c_1847,plain,(
    ! [B_257,A_258] :
      ( m1_pre_topc(B_257,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_258)
      | ~ m1_pre_topc(B_257,A_258)
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | ~ m1_pre_topc(B_257,'#skF_2')
      | ~ m1_pre_topc(B_257,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_364,c_18])).

tff(c_1849,plain,(
    ! [B_257] :
      ( m1_pre_topc(B_257,'#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_257,'#skF_2')
      | ~ m1_pre_topc(B_257,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_1847])).

tff(c_1852,plain,(
    ! [B_257] :
      ( m1_pre_topc(B_257,'#skF_4')
      | ~ m1_pre_topc(B_257,'#skF_2')
      | ~ m1_pre_topc(B_257,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1849])).

tff(c_16002,plain,(
    ! [A_1703,C_1705] :
      ( m1_pre_topc(k2_tsep_1(A_1703,'#skF_2',C_1705),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_1703,'#skF_2',C_1705),'#skF_1')
      | ~ v2_pre_topc(A_1703)
      | ~ v1_pre_topc(k2_tsep_1(A_1703,'#skF_2',C_1705))
      | v2_struct_0(k2_tsep_1(A_1703,'#skF_2',C_1705))
      | r1_tsep_1('#skF_2',C_1705)
      | ~ m1_pre_topc(C_1705,A_1703)
      | v2_struct_0(C_1705)
      | ~ m1_pre_topc('#skF_2',A_1703)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1703)
      | v2_struct_0(A_1703) ) ),
    inference(resolution,[status(thm)],[c_15931,c_1852])).

tff(c_16438,plain,(
    ! [A_1747,C_1748] :
      ( m1_pre_topc(k2_tsep_1(A_1747,'#skF_2',C_1748),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_1747,'#skF_2',C_1748),'#skF_1')
      | ~ v2_pre_topc(A_1747)
      | ~ v1_pre_topc(k2_tsep_1(A_1747,'#skF_2',C_1748))
      | v2_struct_0(k2_tsep_1(A_1747,'#skF_2',C_1748))
      | r1_tsep_1('#skF_2',C_1748)
      | ~ m1_pre_topc(C_1748,A_1747)
      | v2_struct_0(C_1748)
      | ~ m1_pre_topc('#skF_2',A_1747)
      | ~ l1_pre_topc(A_1747)
      | v2_struct_0(A_1747) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_16002])).

tff(c_16442,plain,(
    ! [C_23] :
      ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_23),'#skF_4')
      | ~ v2_pre_topc('#skF_1')
      | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_23))
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_23))
      | r1_tsep_1('#skF_2',C_23)
      | ~ m1_pre_topc(C_23,'#skF_1')
      | v2_struct_0(C_23)
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_16438])).

tff(c_16445,plain,(
    ! [C_23] :
      ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_23),'#skF_4')
      | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_23))
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_23))
      | r1_tsep_1('#skF_2',C_23)
      | ~ m1_pre_topc(C_23,'#skF_1')
      | v2_struct_0(C_23)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_42,c_16442])).

tff(c_16447,plain,(
    ! [C_1749] :
      ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_1749),'#skF_4')
      | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_1749))
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_1749))
      | r1_tsep_1('#skF_2',C_1749)
      | ~ m1_pre_topc(C_1749,'#skF_1')
      | v2_struct_0(C_1749) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_16445])).

tff(c_20,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_16473,plain,
    ( ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_16447,c_20])).

tff(c_16509,plain,
    ( ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16473])).

tff(c_16510,plain,
    ( ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_22,c_16509])).

tff(c_16511,plain,(
    ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_16510])).

tff(c_16514,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_16511])).

tff(c_16517,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_16514])).

tff(c_16519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_16517])).

tff(c_16520,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16510])).

tff(c_14,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ v2_struct_0(k2_tsep_1(A_21,B_22,C_23))
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16524,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16520,c_14])).

tff(c_16527,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_16524])).

tff(c_16529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_16527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.27/7.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.27/7.08  
% 15.27/7.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.27/7.08  %$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.27/7.08  
% 15.27/7.08  %Foreground sorts:
% 15.27/7.08  
% 15.27/7.08  
% 15.27/7.08  %Background operators:
% 15.27/7.08  
% 15.27/7.08  
% 15.27/7.08  %Foreground operators:
% 15.27/7.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.27/7.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.27/7.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.27/7.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.27/7.08  tff('#skF_2', type, '#skF_2': $i).
% 15.27/7.08  tff('#skF_3', type, '#skF_3': $i).
% 15.27/7.08  tff('#skF_1', type, '#skF_1': $i).
% 15.27/7.08  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 15.27/7.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.27/7.08  tff('#skF_4', type, '#skF_4': $i).
% 15.27/7.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.27/7.08  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 15.27/7.08  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 15.27/7.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 15.27/7.08  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 15.27/7.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.27/7.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.27/7.08  
% 15.27/7.10  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, D)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tmap_1)).
% 15.27/7.10  tff(f_87, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 15.27/7.10  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 15.27/7.10  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.27/7.10  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 15.27/7.10  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 15.27/7.10  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_12, plain, (![A_21, B_22, C_23]: (v1_pre_topc(k2_tsep_1(A_21, B_22, C_23)) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.27/7.10  tff(c_22, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_10, plain, (![A_21, B_22, C_23]: (m1_pre_topc(k2_tsep_1(A_21, B_22, C_23), A_21) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.27/7.10  tff(c_766, plain, (![A_142, B_143, C_144]: (u1_struct_0(k2_tsep_1(A_142, B_143, C_144))=k3_xboole_0(u1_struct_0(B_143), u1_struct_0(C_144)) | ~m1_pre_topc(k2_tsep_1(A_142, B_143, C_144), A_142) | ~v1_pre_topc(k2_tsep_1(A_142, B_143, C_144)) | v2_struct_0(k2_tsep_1(A_142, B_143, C_144)) | r1_tsep_1(B_143, C_144) | ~m1_pre_topc(C_144, A_142) | v2_struct_0(C_144) | ~m1_pre_topc(B_143, A_142) | v2_struct_0(B_143) | ~l1_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.27/7.10  tff(c_1021, plain, (![A_176, B_177, C_178]: (u1_struct_0(k2_tsep_1(A_176, B_177, C_178))=k3_xboole_0(u1_struct_0(B_177), u1_struct_0(C_178)) | ~v1_pre_topc(k2_tsep_1(A_176, B_177, C_178)) | v2_struct_0(k2_tsep_1(A_176, B_177, C_178)) | r1_tsep_1(B_177, C_178) | ~m1_pre_topc(C_178, A_176) | v2_struct_0(C_178) | ~m1_pre_topc(B_177, A_176) | v2_struct_0(B_177) | ~l1_pre_topc(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_10, c_766])).
% 15.27/7.10  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.27/7.10  tff(c_1490, plain, (![A_215, B_216, C_217]: (r1_tarski(u1_struct_0(k2_tsep_1(A_215, B_216, C_217)), u1_struct_0(B_216)) | ~v1_pre_topc(k2_tsep_1(A_215, B_216, C_217)) | v2_struct_0(k2_tsep_1(A_215, B_216, C_217)) | r1_tsep_1(B_216, C_217) | ~m1_pre_topc(C_217, A_215) | v2_struct_0(C_217) | ~m1_pre_topc(B_216, A_215) | v2_struct_0(B_216) | ~l1_pre_topc(A_215) | v2_struct_0(A_215))), inference(superposition, [status(thm), theory('equality')], [c_1021, c_2])).
% 15.27/7.10  tff(c_18, plain, (![B_28, C_30, A_24]: (m1_pre_topc(B_28, C_30) | ~r1_tarski(u1_struct_0(B_28), u1_struct_0(C_30)) | ~m1_pre_topc(C_30, A_24) | ~m1_pre_topc(B_28, A_24) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_101])).
% 15.27/7.10  tff(c_10220, plain, (![A_1030, B_1031, C_1032, A_1033]: (m1_pre_topc(k2_tsep_1(A_1030, B_1031, C_1032), B_1031) | ~m1_pre_topc(B_1031, A_1033) | ~m1_pre_topc(k2_tsep_1(A_1030, B_1031, C_1032), A_1033) | ~l1_pre_topc(A_1033) | ~v2_pre_topc(A_1033) | ~v1_pre_topc(k2_tsep_1(A_1030, B_1031, C_1032)) | v2_struct_0(k2_tsep_1(A_1030, B_1031, C_1032)) | r1_tsep_1(B_1031, C_1032) | ~m1_pre_topc(C_1032, A_1030) | v2_struct_0(C_1032) | ~m1_pre_topc(B_1031, A_1030) | v2_struct_0(B_1031) | ~l1_pre_topc(A_1030) | v2_struct_0(A_1030))), inference(resolution, [status(thm)], [c_1490, c_18])).
% 15.27/7.10  tff(c_15931, plain, (![A_1703, B_1704, C_1705]: (m1_pre_topc(k2_tsep_1(A_1703, B_1704, C_1705), B_1704) | ~v2_pre_topc(A_1703) | ~v1_pre_topc(k2_tsep_1(A_1703, B_1704, C_1705)) | v2_struct_0(k2_tsep_1(A_1703, B_1704, C_1705)) | r1_tsep_1(B_1704, C_1705) | ~m1_pre_topc(C_1705, A_1703) | v2_struct_0(C_1705) | ~m1_pre_topc(B_1704, A_1703) | v2_struct_0(B_1704) | ~l1_pre_topc(A_1703) | v2_struct_0(A_1703))), inference(resolution, [status(thm)], [c_10, c_10220])).
% 15.27/7.10  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_26, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_75, plain, (![B_60, C_61, A_62]: (r1_tarski(u1_struct_0(B_60), u1_struct_0(C_61)) | ~m1_pre_topc(B_60, C_61) | ~m1_pre_topc(C_61, A_62) | ~m1_pre_topc(B_60, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_101])).
% 15.27/7.10  tff(c_81, plain, (![B_60]: (r1_tarski(u1_struct_0(B_60), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_60, '#skF_2') | ~m1_pre_topc(B_60, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_75])).
% 15.27/7.10  tff(c_90, plain, (![B_60]: (r1_tarski(u1_struct_0(B_60), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_60, '#skF_2') | ~m1_pre_topc(B_60, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_81])).
% 15.27/7.10  tff(c_83, plain, (![B_60]: (r1_tarski(u1_struct_0(B_60), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_60, '#skF_4') | ~m1_pre_topc(B_60, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_75])).
% 15.27/7.10  tff(c_121, plain, (![B_68]: (r1_tarski(u1_struct_0(B_68), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_68, '#skF_4') | ~m1_pre_topc(B_68, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_83])).
% 15.27/7.10  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.27/7.10  tff(c_296, plain, (![A_100, B_101]: (r1_tarski(A_100, u1_struct_0('#skF_4')) | ~r1_tarski(A_100, u1_struct_0(B_101)) | ~m1_pre_topc(B_101, '#skF_4') | ~m1_pre_topc(B_101, '#skF_1'))), inference(resolution, [status(thm)], [c_121, c_4])).
% 15.27/7.10  tff(c_312, plain, (![B_60]: (r1_tarski(u1_struct_0(B_60), u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | ~m1_pre_topc(B_60, '#skF_2') | ~m1_pre_topc(B_60, '#skF_1'))), inference(resolution, [status(thm)], [c_90, c_296])).
% 15.27/7.10  tff(c_364, plain, (![B_103]: (r1_tarski(u1_struct_0(B_103), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_103, '#skF_2') | ~m1_pre_topc(B_103, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_312])).
% 15.27/7.10  tff(c_1847, plain, (![B_257, A_258]: (m1_pre_topc(B_257, '#skF_4') | ~m1_pre_topc('#skF_4', A_258) | ~m1_pre_topc(B_257, A_258) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | ~m1_pre_topc(B_257, '#skF_2') | ~m1_pre_topc(B_257, '#skF_1'))), inference(resolution, [status(thm)], [c_364, c_18])).
% 15.27/7.10  tff(c_1849, plain, (![B_257]: (m1_pre_topc(B_257, '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(B_257, '#skF_2') | ~m1_pre_topc(B_257, '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_1847])).
% 15.27/7.10  tff(c_1852, plain, (![B_257]: (m1_pre_topc(B_257, '#skF_4') | ~m1_pre_topc(B_257, '#skF_2') | ~m1_pre_topc(B_257, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1849])).
% 15.27/7.10  tff(c_16002, plain, (![A_1703, C_1705]: (m1_pre_topc(k2_tsep_1(A_1703, '#skF_2', C_1705), '#skF_4') | ~m1_pre_topc(k2_tsep_1(A_1703, '#skF_2', C_1705), '#skF_1') | ~v2_pre_topc(A_1703) | ~v1_pre_topc(k2_tsep_1(A_1703, '#skF_2', C_1705)) | v2_struct_0(k2_tsep_1(A_1703, '#skF_2', C_1705)) | r1_tsep_1('#skF_2', C_1705) | ~m1_pre_topc(C_1705, A_1703) | v2_struct_0(C_1705) | ~m1_pre_topc('#skF_2', A_1703) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1703) | v2_struct_0(A_1703))), inference(resolution, [status(thm)], [c_15931, c_1852])).
% 15.27/7.10  tff(c_16438, plain, (![A_1747, C_1748]: (m1_pre_topc(k2_tsep_1(A_1747, '#skF_2', C_1748), '#skF_4') | ~m1_pre_topc(k2_tsep_1(A_1747, '#skF_2', C_1748), '#skF_1') | ~v2_pre_topc(A_1747) | ~v1_pre_topc(k2_tsep_1(A_1747, '#skF_2', C_1748)) | v2_struct_0(k2_tsep_1(A_1747, '#skF_2', C_1748)) | r1_tsep_1('#skF_2', C_1748) | ~m1_pre_topc(C_1748, A_1747) | v2_struct_0(C_1748) | ~m1_pre_topc('#skF_2', A_1747) | ~l1_pre_topc(A_1747) | v2_struct_0(A_1747))), inference(negUnitSimplification, [status(thm)], [c_38, c_16002])).
% 15.27/7.10  tff(c_16442, plain, (![C_23]: (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_23), '#skF_4') | ~v2_pre_topc('#skF_1') | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_23)) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_23)) | r1_tsep_1('#skF_2', C_23) | ~m1_pre_topc(C_23, '#skF_1') | v2_struct_0(C_23) | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_16438])).
% 15.27/7.10  tff(c_16445, plain, (![C_23]: (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_23), '#skF_4') | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_23)) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_23)) | r1_tsep_1('#skF_2', C_23) | ~m1_pre_topc(C_23, '#skF_1') | v2_struct_0(C_23) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_42, c_16442])).
% 15.27/7.10  tff(c_16447, plain, (![C_1749]: (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_1749), '#skF_4') | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_1749)) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_1749)) | r1_tsep_1('#skF_2', C_1749) | ~m1_pre_topc(C_1749, '#skF_1') | v2_struct_0(C_1749))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_16445])).
% 15.27/7.10  tff(c_20, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/7.10  tff(c_16473, plain, (~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_16447, c_20])).
% 15.27/7.10  tff(c_16509, plain, (~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16473])).
% 15.27/7.10  tff(c_16510, plain, (~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_34, c_22, c_16509])).
% 15.27/7.10  tff(c_16511, plain, (~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_16510])).
% 15.27/7.10  tff(c_16514, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_16511])).
% 15.27/7.10  tff(c_16517, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_16514])).
% 15.27/7.10  tff(c_16519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_16517])).
% 15.27/7.10  tff(c_16520, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_16510])).
% 15.27/7.10  tff(c_14, plain, (![A_21, B_22, C_23]: (~v2_struct_0(k2_tsep_1(A_21, B_22, C_23)) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.27/7.10  tff(c_16524, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16520, c_14])).
% 15.27/7.10  tff(c_16527, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_16524])).
% 15.27/7.10  tff(c_16529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_16527])).
% 15.27/7.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.27/7.10  
% 15.27/7.10  Inference rules
% 15.27/7.10  ----------------------
% 15.27/7.10  #Ref     : 2
% 15.27/7.10  #Sup     : 4106
% 15.27/7.10  #Fact    : 2
% 15.27/7.10  #Define  : 0
% 15.27/7.10  #Split   : 9
% 15.27/7.10  #Chain   : 0
% 15.27/7.10  #Close   : 0
% 15.27/7.10  
% 15.27/7.10  Ordering : KBO
% 15.27/7.10  
% 15.27/7.10  Simplification rules
% 15.27/7.10  ----------------------
% 15.27/7.10  #Subsume      : 1002
% 15.27/7.10  #Demod        : 675
% 15.27/7.10  #Tautology    : 129
% 15.27/7.10  #SimpNegUnit  : 51
% 15.27/7.10  #BackRed      : 0
% 15.27/7.10  
% 15.27/7.10  #Partial instantiations: 0
% 15.27/7.10  #Strategies tried      : 1
% 15.27/7.10  
% 15.27/7.10  Timing (in seconds)
% 15.27/7.10  ----------------------
% 15.27/7.10  Preprocessing        : 0.31
% 15.27/7.10  Parsing              : 0.17
% 15.27/7.10  CNF conversion       : 0.02
% 15.27/7.10  Main loop            : 6.04
% 15.27/7.10  Inferencing          : 1.23
% 15.54/7.10  Reduction            : 1.16
% 15.54/7.10  Demodulation         : 0.84
% 15.54/7.10  BG Simplification    : 0.13
% 15.54/7.10  Subsumption          : 3.20
% 15.54/7.10  Abstraction          : 0.18
% 15.54/7.10  MUC search           : 0.00
% 15.54/7.11  Cooper               : 0.00
% 15.54/7.11  Total                : 6.38
% 15.54/7.11  Index Insertion      : 0.00
% 15.54/7.11  Index Deletion       : 0.00
% 15.54/7.11  Index Matching       : 0.00
% 15.54/7.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
