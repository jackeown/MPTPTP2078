%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:43 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 124 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  262 ( 719 expanded)
%              Number of equality atoms :    8 (  13 expanded)
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

tff(f_149,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

tff(f_101,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_79,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_28,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_42,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_16,plain,(
    ! [A_24,B_25,C_26] :
      ( m1_pre_topc(k2_tsep_1(A_24,B_25,C_26),A_24)
      | ~ m1_pre_topc(C_26,A_24)
      | v2_struct_0(C_26)
      | ~ m1_pre_topc(B_25,A_24)
      | v2_struct_0(B_25)
      | ~ l1_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_18,plain,(
    ! [A_24,B_25,C_26] :
      ( v1_pre_topc(k2_tsep_1(A_24,B_25,C_26))
      | ~ m1_pre_topc(C_26,A_24)
      | v2_struct_0(C_26)
      | ~ m1_pre_topc(B_25,A_24)
      | v2_struct_0(B_25)
      | ~ l1_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_639,plain,(
    ! [A_122,B_123,C_124] :
      ( u1_struct_0(k2_tsep_1(A_122,B_123,C_124)) = k3_xboole_0(u1_struct_0(B_123),u1_struct_0(C_124))
      | ~ m1_pre_topc(k2_tsep_1(A_122,B_123,C_124),A_122)
      | ~ v1_pre_topc(k2_tsep_1(A_122,B_123,C_124))
      | v2_struct_0(k2_tsep_1(A_122,B_123,C_124))
      | r1_tsep_1(B_123,C_124)
      | ~ m1_pre_topc(C_124,A_122)
      | v2_struct_0(C_124)
      | ~ m1_pre_topc(B_123,A_122)
      | v2_struct_0(B_123)
      | ~ l1_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_643,plain,(
    ! [A_125,B_126,C_127] :
      ( u1_struct_0(k2_tsep_1(A_125,B_126,C_127)) = k3_xboole_0(u1_struct_0(B_126),u1_struct_0(C_127))
      | ~ v1_pre_topc(k2_tsep_1(A_125,B_126,C_127))
      | v2_struct_0(k2_tsep_1(A_125,B_126,C_127))
      | r1_tsep_1(B_126,C_127)
      | ~ m1_pre_topc(C_127,A_125)
      | v2_struct_0(C_127)
      | ~ m1_pre_topc(B_126,A_125)
      | v2_struct_0(B_126)
      | ~ l1_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_16,c_639])).

tff(c_20,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ v2_struct_0(k2_tsep_1(A_24,B_25,C_26))
      | ~ m1_pre_topc(C_26,A_24)
      | v2_struct_0(C_26)
      | ~ m1_pre_topc(B_25,A_24)
      | v2_struct_0(B_25)
      | ~ l1_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_722,plain,(
    ! [A_128,B_129,C_130] :
      ( u1_struct_0(k2_tsep_1(A_128,B_129,C_130)) = k3_xboole_0(u1_struct_0(B_129),u1_struct_0(C_130))
      | ~ v1_pre_topc(k2_tsep_1(A_128,B_129,C_130))
      | r1_tsep_1(B_129,C_130)
      | ~ m1_pre_topc(C_130,A_128)
      | v2_struct_0(C_130)
      | ~ m1_pre_topc(B_129,A_128)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_643,c_20])).

tff(c_725,plain,(
    ! [A_24,B_25,C_26] :
      ( u1_struct_0(k2_tsep_1(A_24,B_25,C_26)) = k3_xboole_0(u1_struct_0(B_25),u1_struct_0(C_26))
      | r1_tsep_1(B_25,C_26)
      | ~ m1_pre_topc(C_26,A_24)
      | v2_struct_0(C_26)
      | ~ m1_pre_topc(B_25,A_24)
      | v2_struct_0(B_25)
      | ~ l1_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_18,c_722])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_53,plain,(
    ! [B_46,A_47] :
      ( l1_pre_topc(B_46)
      | ~ m1_pre_topc(B_46,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_73,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_62])).

tff(c_726,plain,(
    ! [A_131,B_132,C_133] :
      ( u1_struct_0(k2_tsep_1(A_131,B_132,C_133)) = k3_xboole_0(u1_struct_0(B_132),u1_struct_0(C_133))
      | r1_tsep_1(B_132,C_133)
      | ~ m1_pre_topc(C_133,A_131)
      | v2_struct_0(C_133)
      | ~ m1_pre_topc(B_132,A_131)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_18,c_722])).

tff(c_91,plain,(
    ! [B_50,A_51] :
      ( v2_pre_topc(B_50)
      | ~ m1_pre_topc(B_50,A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_100,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_91])).

tff(c_115,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_100])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_219,plain,(
    ! [B_61,C_62,A_63] :
      ( m1_pre_topc(B_61,C_62)
      | ~ r1_tarski(u1_struct_0(B_61),u1_struct_0(C_62))
      | ~ m1_pre_topc(C_62,A_63)
      | ~ m1_pre_topc(B_61,A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_239,plain,(
    ! [B_64,A_65] :
      ( m1_pre_topc(B_64,B_64)
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_219])).

tff(c_245,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_239])).

tff(c_258,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_245])).

tff(c_22,plain,(
    ! [B_31,C_33,A_27] :
      ( r1_tarski(u1_struct_0(B_31),u1_struct_0(C_33))
      | ~ m1_pre_topc(B_31,C_33)
      | ~ m1_pre_topc(C_33,A_27)
      | ~ m1_pre_topc(B_31,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_313,plain,(
    ! [B_31] :
      ( r1_tarski(u1_struct_0(B_31),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_31,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_258,c_22])).

tff(c_325,plain,(
    ! [B_31] :
      ( r1_tarski(u1_struct_0(B_31),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_31,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_73,c_313])).

tff(c_832,plain,(
    ! [B_141,C_142,A_143] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_141),u1_struct_0(C_142)),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(k2_tsep_1(A_143,B_141,C_142),'#skF_4')
      | r1_tsep_1(B_141,C_142)
      | ~ m1_pre_topc(C_142,A_143)
      | v2_struct_0(C_142)
      | ~ m1_pre_topc(B_141,A_143)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_325])).

tff(c_835,plain,(
    ! [B_25,C_26] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_25),u1_struct_0(C_26)),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_25,C_26)
      | ~ m1_pre_topc(C_26,'#skF_4')
      | v2_struct_0(C_26)
      | ~ m1_pre_topc(B_25,'#skF_4')
      | v2_struct_0(B_25)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_832])).

tff(c_838,plain,(
    ! [B_25,C_26] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_25),u1_struct_0(C_26)),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_25,C_26)
      | ~ m1_pre_topc(C_26,'#skF_4')
      | v2_struct_0(C_26)
      | ~ m1_pre_topc(B_25,'#skF_4')
      | v2_struct_0(B_25)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_835])).

tff(c_840,plain,(
    ! [B_144,C_145] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_144),u1_struct_0(C_145)),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_144,C_145)
      | ~ m1_pre_topc(C_145,'#skF_4')
      | v2_struct_0(C_145)
      | ~ m1_pre_topc(B_144,'#skF_4')
      | v2_struct_0(B_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_838])).

tff(c_952,plain,(
    ! [A_175,B_176,C_177] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_175,B_176,C_177)),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_176,C_177)
      | ~ m1_pre_topc(C_177,'#skF_4')
      | v2_struct_0(C_177)
      | ~ m1_pre_topc(B_176,'#skF_4')
      | v2_struct_0(B_176)
      | r1_tsep_1(B_176,C_177)
      | ~ m1_pre_topc(C_177,A_175)
      | v2_struct_0(C_177)
      | ~ m1_pre_topc(B_176,A_175)
      | v2_struct_0(B_176)
      | ~ l1_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_840])).

tff(c_24,plain,(
    ! [B_31,C_33,A_27] :
      ( m1_pre_topc(B_31,C_33)
      | ~ r1_tarski(u1_struct_0(B_31),u1_struct_0(C_33))
      | ~ m1_pre_topc(C_33,A_27)
      | ~ m1_pre_topc(B_31,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1069,plain,(
    ! [A_213,B_214,C_215,A_216] :
      ( m1_pre_topc(k2_tsep_1(A_213,B_214,C_215),'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_216)
      | ~ m1_pre_topc(k2_tsep_1(A_213,B_214,C_215),A_216)
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | ~ m1_pre_topc(C_215,'#skF_4')
      | ~ m1_pre_topc(B_214,'#skF_4')
      | r1_tsep_1(B_214,C_215)
      | ~ m1_pre_topc(C_215,A_213)
      | v2_struct_0(C_215)
      | ~ m1_pre_topc(B_214,A_213)
      | v2_struct_0(B_214)
      | ~ l1_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(resolution,[status(thm)],[c_952,c_24])).

tff(c_1076,plain,(
    ! [A_217,B_218,C_219] :
      ( m1_pre_topc(k2_tsep_1(A_217,B_218,C_219),'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_217)
      | ~ v2_pre_topc(A_217)
      | ~ m1_pre_topc(C_219,'#skF_4')
      | ~ m1_pre_topc(B_218,'#skF_4')
      | r1_tsep_1(B_218,C_219)
      | ~ m1_pre_topc(C_219,A_217)
      | v2_struct_0(C_219)
      | ~ m1_pre_topc(B_218,A_217)
      | v2_struct_0(B_218)
      | ~ l1_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_16,c_1069])).

tff(c_26,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1096,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1076,c_26])).

tff(c_1116,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_38,c_32,c_30,c_48,c_34,c_1096])).

tff(c_1118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_40,c_28,c_1116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.18/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.74  
% 4.18/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.74  %$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.18/1.74  
% 4.18/1.74  %Foreground sorts:
% 4.18/1.74  
% 4.18/1.74  
% 4.18/1.74  %Background operators:
% 4.18/1.74  
% 4.18/1.74  
% 4.18/1.74  %Foreground operators:
% 4.18/1.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.18/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.18/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.18/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.18/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.18/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.18/1.74  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.18/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.18/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.74  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.18/1.74  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 4.18/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.18/1.74  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.18/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.18/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.18/1.74  
% 4.18/1.76  tff(f_149, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, D)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tmap_1)).
% 4.18/1.76  tff(f_101, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 4.18/1.76  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tsep_1)).
% 4.18/1.76  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.18/1.76  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.18/1.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.18/1.76  tff(f_115, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.18/1.76  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_28, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_42, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.18/1.76  tff(c_16, plain, (![A_24, B_25, C_26]: (m1_pre_topc(k2_tsep_1(A_24, B_25, C_26), A_24) | ~m1_pre_topc(C_26, A_24) | v2_struct_0(C_26) | ~m1_pre_topc(B_25, A_24) | v2_struct_0(B_25) | ~l1_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.18/1.76  tff(c_18, plain, (![A_24, B_25, C_26]: (v1_pre_topc(k2_tsep_1(A_24, B_25, C_26)) | ~m1_pre_topc(C_26, A_24) | v2_struct_0(C_26) | ~m1_pre_topc(B_25, A_24) | v2_struct_0(B_25) | ~l1_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.18/1.76  tff(c_639, plain, (![A_122, B_123, C_124]: (u1_struct_0(k2_tsep_1(A_122, B_123, C_124))=k3_xboole_0(u1_struct_0(B_123), u1_struct_0(C_124)) | ~m1_pre_topc(k2_tsep_1(A_122, B_123, C_124), A_122) | ~v1_pre_topc(k2_tsep_1(A_122, B_123, C_124)) | v2_struct_0(k2_tsep_1(A_122, B_123, C_124)) | r1_tsep_1(B_123, C_124) | ~m1_pre_topc(C_124, A_122) | v2_struct_0(C_124) | ~m1_pre_topc(B_123, A_122) | v2_struct_0(B_123) | ~l1_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.45/1.76  tff(c_643, plain, (![A_125, B_126, C_127]: (u1_struct_0(k2_tsep_1(A_125, B_126, C_127))=k3_xboole_0(u1_struct_0(B_126), u1_struct_0(C_127)) | ~v1_pre_topc(k2_tsep_1(A_125, B_126, C_127)) | v2_struct_0(k2_tsep_1(A_125, B_126, C_127)) | r1_tsep_1(B_126, C_127) | ~m1_pre_topc(C_127, A_125) | v2_struct_0(C_127) | ~m1_pre_topc(B_126, A_125) | v2_struct_0(B_126) | ~l1_pre_topc(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_16, c_639])).
% 4.45/1.76  tff(c_20, plain, (![A_24, B_25, C_26]: (~v2_struct_0(k2_tsep_1(A_24, B_25, C_26)) | ~m1_pre_topc(C_26, A_24) | v2_struct_0(C_26) | ~m1_pre_topc(B_25, A_24) | v2_struct_0(B_25) | ~l1_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.45/1.76  tff(c_722, plain, (![A_128, B_129, C_130]: (u1_struct_0(k2_tsep_1(A_128, B_129, C_130))=k3_xboole_0(u1_struct_0(B_129), u1_struct_0(C_130)) | ~v1_pre_topc(k2_tsep_1(A_128, B_129, C_130)) | r1_tsep_1(B_129, C_130) | ~m1_pre_topc(C_130, A_128) | v2_struct_0(C_130) | ~m1_pre_topc(B_129, A_128) | v2_struct_0(B_129) | ~l1_pre_topc(A_128) | v2_struct_0(A_128))), inference(resolution, [status(thm)], [c_643, c_20])).
% 4.45/1.76  tff(c_725, plain, (![A_24, B_25, C_26]: (u1_struct_0(k2_tsep_1(A_24, B_25, C_26))=k3_xboole_0(u1_struct_0(B_25), u1_struct_0(C_26)) | r1_tsep_1(B_25, C_26) | ~m1_pre_topc(C_26, A_24) | v2_struct_0(C_26) | ~m1_pre_topc(B_25, A_24) | v2_struct_0(B_25) | ~l1_pre_topc(A_24) | v2_struct_0(A_24))), inference(resolution, [status(thm)], [c_18, c_722])).
% 4.45/1.76  tff(c_36, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.45/1.76  tff(c_53, plain, (![B_46, A_47]: (l1_pre_topc(B_46) | ~m1_pre_topc(B_46, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.45/1.76  tff(c_62, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_53])).
% 4.45/1.76  tff(c_73, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_62])).
% 4.45/1.76  tff(c_726, plain, (![A_131, B_132, C_133]: (u1_struct_0(k2_tsep_1(A_131, B_132, C_133))=k3_xboole_0(u1_struct_0(B_132), u1_struct_0(C_133)) | r1_tsep_1(B_132, C_133) | ~m1_pre_topc(C_133, A_131) | v2_struct_0(C_133) | ~m1_pre_topc(B_132, A_131) | v2_struct_0(B_132) | ~l1_pre_topc(A_131) | v2_struct_0(A_131))), inference(resolution, [status(thm)], [c_18, c_722])).
% 4.45/1.76  tff(c_91, plain, (![B_50, A_51]: (v2_pre_topc(B_50) | ~m1_pre_topc(B_50, A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.45/1.76  tff(c_100, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_91])).
% 4.45/1.76  tff(c_115, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_100])).
% 4.45/1.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.45/1.76  tff(c_219, plain, (![B_61, C_62, A_63]: (m1_pre_topc(B_61, C_62) | ~r1_tarski(u1_struct_0(B_61), u1_struct_0(C_62)) | ~m1_pre_topc(C_62, A_63) | ~m1_pre_topc(B_61, A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.45/1.76  tff(c_239, plain, (![B_64, A_65]: (m1_pre_topc(B_64, B_64) | ~m1_pre_topc(B_64, A_65) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(resolution, [status(thm)], [c_6, c_219])).
% 4.45/1.76  tff(c_245, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_239])).
% 4.45/1.76  tff(c_258, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_245])).
% 4.45/1.76  tff(c_22, plain, (![B_31, C_33, A_27]: (r1_tarski(u1_struct_0(B_31), u1_struct_0(C_33)) | ~m1_pre_topc(B_31, C_33) | ~m1_pre_topc(C_33, A_27) | ~m1_pre_topc(B_31, A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.45/1.76  tff(c_313, plain, (![B_31]: (r1_tarski(u1_struct_0(B_31), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_31, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_258, c_22])).
% 4.45/1.76  tff(c_325, plain, (![B_31]: (r1_tarski(u1_struct_0(B_31), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_31, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_73, c_313])).
% 4.45/1.76  tff(c_832, plain, (![B_141, C_142, A_143]: (r1_tarski(k3_xboole_0(u1_struct_0(B_141), u1_struct_0(C_142)), u1_struct_0('#skF_4')) | ~m1_pre_topc(k2_tsep_1(A_143, B_141, C_142), '#skF_4') | r1_tsep_1(B_141, C_142) | ~m1_pre_topc(C_142, A_143) | v2_struct_0(C_142) | ~m1_pre_topc(B_141, A_143) | v2_struct_0(B_141) | ~l1_pre_topc(A_143) | v2_struct_0(A_143))), inference(superposition, [status(thm), theory('equality')], [c_726, c_325])).
% 4.45/1.76  tff(c_835, plain, (![B_25, C_26]: (r1_tarski(k3_xboole_0(u1_struct_0(B_25), u1_struct_0(C_26)), u1_struct_0('#skF_4')) | r1_tsep_1(B_25, C_26) | ~m1_pre_topc(C_26, '#skF_4') | v2_struct_0(C_26) | ~m1_pre_topc(B_25, '#skF_4') | v2_struct_0(B_25) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_832])).
% 4.45/1.76  tff(c_838, plain, (![B_25, C_26]: (r1_tarski(k3_xboole_0(u1_struct_0(B_25), u1_struct_0(C_26)), u1_struct_0('#skF_4')) | r1_tsep_1(B_25, C_26) | ~m1_pre_topc(C_26, '#skF_4') | v2_struct_0(C_26) | ~m1_pre_topc(B_25, '#skF_4') | v2_struct_0(B_25) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_835])).
% 4.45/1.76  tff(c_840, plain, (![B_144, C_145]: (r1_tarski(k3_xboole_0(u1_struct_0(B_144), u1_struct_0(C_145)), u1_struct_0('#skF_4')) | r1_tsep_1(B_144, C_145) | ~m1_pre_topc(C_145, '#skF_4') | v2_struct_0(C_145) | ~m1_pre_topc(B_144, '#skF_4') | v2_struct_0(B_144))), inference(negUnitSimplification, [status(thm)], [c_36, c_838])).
% 4.45/1.76  tff(c_952, plain, (![A_175, B_176, C_177]: (r1_tarski(u1_struct_0(k2_tsep_1(A_175, B_176, C_177)), u1_struct_0('#skF_4')) | r1_tsep_1(B_176, C_177) | ~m1_pre_topc(C_177, '#skF_4') | v2_struct_0(C_177) | ~m1_pre_topc(B_176, '#skF_4') | v2_struct_0(B_176) | r1_tsep_1(B_176, C_177) | ~m1_pre_topc(C_177, A_175) | v2_struct_0(C_177) | ~m1_pre_topc(B_176, A_175) | v2_struct_0(B_176) | ~l1_pre_topc(A_175) | v2_struct_0(A_175))), inference(superposition, [status(thm), theory('equality')], [c_725, c_840])).
% 4.45/1.76  tff(c_24, plain, (![B_31, C_33, A_27]: (m1_pre_topc(B_31, C_33) | ~r1_tarski(u1_struct_0(B_31), u1_struct_0(C_33)) | ~m1_pre_topc(C_33, A_27) | ~m1_pre_topc(B_31, A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.45/1.76  tff(c_1069, plain, (![A_213, B_214, C_215, A_216]: (m1_pre_topc(k2_tsep_1(A_213, B_214, C_215), '#skF_4') | ~m1_pre_topc('#skF_4', A_216) | ~m1_pre_topc(k2_tsep_1(A_213, B_214, C_215), A_216) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | ~m1_pre_topc(C_215, '#skF_4') | ~m1_pre_topc(B_214, '#skF_4') | r1_tsep_1(B_214, C_215) | ~m1_pre_topc(C_215, A_213) | v2_struct_0(C_215) | ~m1_pre_topc(B_214, A_213) | v2_struct_0(B_214) | ~l1_pre_topc(A_213) | v2_struct_0(A_213))), inference(resolution, [status(thm)], [c_952, c_24])).
% 4.45/1.76  tff(c_1076, plain, (![A_217, B_218, C_219]: (m1_pre_topc(k2_tsep_1(A_217, B_218, C_219), '#skF_4') | ~m1_pre_topc('#skF_4', A_217) | ~v2_pre_topc(A_217) | ~m1_pre_topc(C_219, '#skF_4') | ~m1_pre_topc(B_218, '#skF_4') | r1_tsep_1(B_218, C_219) | ~m1_pre_topc(C_219, A_217) | v2_struct_0(C_219) | ~m1_pre_topc(B_218, A_217) | v2_struct_0(B_218) | ~l1_pre_topc(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_16, c_1069])).
% 4.45/1.76  tff(c_26, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.45/1.76  tff(c_1096, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_4') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1076, c_26])).
% 4.45/1.76  tff(c_1116, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_38, c_32, c_30, c_48, c_34, c_1096])).
% 4.45/1.76  tff(c_1118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_40, c_28, c_1116])).
% 4.45/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.76  
% 4.45/1.76  Inference rules
% 4.45/1.76  ----------------------
% 4.45/1.76  #Ref     : 0
% 4.45/1.76  #Sup     : 244
% 4.45/1.76  #Fact    : 0
% 4.45/1.76  #Define  : 0
% 4.45/1.76  #Split   : 3
% 4.45/1.76  #Chain   : 0
% 4.45/1.76  #Close   : 0
% 4.45/1.76  
% 4.45/1.76  Ordering : KBO
% 4.45/1.76  
% 4.45/1.76  Simplification rules
% 4.45/1.76  ----------------------
% 4.45/1.76  #Subsume      : 44
% 4.45/1.76  #Demod        : 135
% 4.45/1.76  #Tautology    : 44
% 4.45/1.76  #SimpNegUnit  : 7
% 4.45/1.76  #BackRed      : 0
% 4.45/1.76  
% 4.45/1.76  #Partial instantiations: 0
% 4.45/1.76  #Strategies tried      : 1
% 4.45/1.76  
% 4.45/1.76  Timing (in seconds)
% 4.45/1.76  ----------------------
% 4.45/1.76  Preprocessing        : 0.31
% 4.45/1.76  Parsing              : 0.16
% 4.45/1.76  CNF conversion       : 0.03
% 4.45/1.76  Main loop            : 0.64
% 4.45/1.76  Inferencing          : 0.24
% 4.45/1.76  Reduction            : 0.17
% 4.45/1.76  Demodulation         : 0.11
% 4.45/1.76  BG Simplification    : 0.03
% 4.45/1.76  Subsumption          : 0.17
% 4.45/1.76  Abstraction          : 0.03
% 4.45/1.76  MUC search           : 0.00
% 4.45/1.76  Cooper               : 0.00
% 4.45/1.76  Total                : 0.98
% 4.45/1.76  Index Insertion      : 0.00
% 4.45/1.76  Index Deletion       : 0.00
% 4.45/1.76  Index Matching       : 0.00
% 4.45/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
