%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1730+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:18 EST 2020

% Result     : Theorem 24.18s
% Output     : CNFRefutation 24.49s
% Verified   : 
% Statistics : Number of formulae       :  419 (5789 expanded)
%              Number of leaves         :   36 (1809 expanded)
%              Depth                    :   46
%              Number of atoms          : 1160 (27186 expanded)
%              Number of equality atoms :  113 (1478 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_tsep_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_182,negated_conjecture,(
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
                   => ( ~ ( ~ r1_tsep_1(k1_tsep_1(A,B,C),D)
                          & r1_tsep_1(B,D)
                          & r1_tsep_1(C,D) )
                      & ~ ( ~ ( r1_tsep_1(B,D)
                              & r1_tsep_1(C,D) )
                          & r1_tsep_1(k1_tsep_1(A,B,C),D) )
                      & ~ ( ~ r1_tsep_1(D,k1_tsep_1(A,B,C))
                          & r1_tsep_1(D,B)
                          & r1_tsep_1(D,C) )
                      & ~ ( ~ ( r1_tsep_1(D,B)
                              & r1_tsep_1(D,C) )
                          & r1_tsep_1(D,k1_tsep_1(A,B,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tmap_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_102,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_118,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_120,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_36865,plain,(
    ! [B_674,A_675] :
      ( l1_pre_topc(B_674)
      | ~ m1_pre_topc(B_674,A_675)
      | ~ l1_pre_topc(A_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36871,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_36865])).

tff(c_36880,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36871])).

tff(c_22,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_36874,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_36865])).

tff(c_36883,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36874])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_67439,plain,(
    ! [A_1126,B_1127,C_1128] :
      ( m1_pre_topc(k1_tsep_1(A_1126,B_1127,C_1128),A_1126)
      | ~ m1_pre_topc(C_1128,A_1126)
      | v2_struct_0(C_1128)
      | ~ m1_pre_topc(B_1127,A_1126)
      | v2_struct_0(B_1127)
      | ~ l1_pre_topc(A_1126)
      | v2_struct_0(A_1126) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [B_29,A_27] :
      ( l1_pre_topc(B_29)
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_69102,plain,(
    ! [A_1164,B_1165,C_1166] :
      ( l1_pre_topc(k1_tsep_1(A_1164,B_1165,C_1166))
      | ~ m1_pre_topc(C_1166,A_1164)
      | v2_struct_0(C_1166)
      | ~ m1_pre_topc(B_1165,A_1164)
      | v2_struct_0(B_1165)
      | ~ l1_pre_topc(A_1164)
      | v2_struct_0(A_1164) ) ),
    inference(resolution,[status(thm)],[c_67439,c_24])).

tff(c_35434,plain,(
    ! [A_638,B_639,C_640] :
      ( m1_pre_topc(k1_tsep_1(A_638,B_639,C_640),A_638)
      | ~ m1_pre_topc(C_640,A_638)
      | v2_struct_0(C_640)
      | ~ m1_pre_topc(B_639,A_638)
      | v2_struct_0(B_639)
      | ~ l1_pre_topc(A_638)
      | v2_struct_0(A_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36854,plain,(
    ! [A_671,B_672,C_673] :
      ( l1_pre_topc(k1_tsep_1(A_671,B_672,C_673))
      | ~ m1_pre_topc(C_673,A_671)
      | v2_struct_0(C_673)
      | ~ m1_pre_topc(B_672,A_671)
      | v2_struct_0(B_672)
      | ~ l1_pre_topc(A_671)
      | v2_struct_0(A_671) ) ),
    inference(resolution,[status(thm)],[c_35434,c_24])).

tff(c_197,plain,(
    ! [B_61,A_62] :
      ( l1_pre_topc(B_61)
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_206,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_197])).

tff(c_215,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_206])).

tff(c_56,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_196,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_116,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_685,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_116])).

tff(c_686,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_685])).

tff(c_203,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_197])).

tff(c_212,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_203])).

tff(c_216,plain,(
    ! [B_63,A_64] :
      ( r1_tsep_1(B_63,A_64)
      | ~ r1_tsep_1(A_64,B_63)
      | ~ l1_struct_0(B_63)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_219,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_216])).

tff(c_1589,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_1592,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1589])).

tff(c_1596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_1592])).

tff(c_1598,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_18,plain,(
    ! [A_23,B_24,C_25] :
      ( v1_pre_topc(k1_tsep_1(A_23,B_24,C_25))
      | ~ m1_pre_topc(C_25,A_23)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc(B_24,A_23)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_128,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_132,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_128])).

tff(c_133,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_26])).

tff(c_1532,plain,(
    ! [A_120,B_121,C_122] :
      ( m1_pre_topc(k1_tsep_1(A_120,B_121,C_122),A_120)
      | ~ m1_pre_topc(C_122,A_120)
      | v2_struct_0(C_122)
      | ~ m1_pre_topc(B_121,A_120)
      | v2_struct_0(B_121)
      | ~ l1_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3218,plain,(
    ! [A_157,B_158,C_159] :
      ( l1_pre_topc(k1_tsep_1(A_157,B_158,C_159))
      | ~ m1_pre_topc(C_159,A_157)
      | v2_struct_0(C_159)
      | ~ m1_pre_topc(B_158,A_157)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_1532,c_24])).

tff(c_1597,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_1600,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1597])).

tff(c_1604,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_1600])).

tff(c_3221,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3218,c_1604])).

tff(c_3224,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_3221])).

tff(c_3226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_3224])).

tff(c_3228,plain,(
    l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1597])).

tff(c_3227,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1597])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_290,plain,(
    ! [A_80,B_81] :
      ( r1_xboole_0(u1_struct_0(A_80),u1_struct_0(B_81))
      | ~ r1_tsep_1(A_80,B_81)
      | ~ l1_struct_0(B_81)
      | ~ l1_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3987,plain,(
    ! [A_175,B_176] :
      ( k3_xboole_0(u1_struct_0(A_175),u1_struct_0(B_176)) = k1_xboole_0
      | ~ r1_tsep_1(A_175,B_176)
      | ~ l1_struct_0(B_176)
      | ~ l1_struct_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_290,c_12])).

tff(c_32,plain,(
    ! [A_34] : k2_xboole_0(A_34,k1_xboole_0) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_225,plain,(
    ! [A_67,B_68,C_69] : k2_xboole_0(k3_xboole_0(A_67,B_68),k3_xboole_0(A_67,C_69)) = k3_xboole_0(A_67,k2_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    ! [B_31,A_30] :
      ( ~ v1_xboole_0(k2_xboole_0(B_31,A_30))
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_249,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ v1_xboole_0(k3_xboole_0(A_70,k2_xboole_0(B_71,C_72)))
      | v1_xboole_0(k3_xboole_0(A_70,C_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_28])).

tff(c_263,plain,(
    ! [A_70,A_34] :
      ( ~ v1_xboole_0(k3_xboole_0(A_70,A_34))
      | v1_xboole_0(k3_xboole_0(A_70,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_249])).

tff(c_4019,plain,(
    ! [A_175,B_176] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k3_xboole_0(u1_struct_0(A_175),k1_xboole_0))
      | ~ r1_tsep_1(A_175,B_176)
      | ~ l1_struct_0(B_176)
      | ~ l1_struct_0(A_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3987,c_263])).

tff(c_4408,plain,(
    ! [A_184,B_185] :
      ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(A_184)))
      | ~ r1_tsep_1(A_184,B_185)
      | ~ l1_struct_0(B_185)
      | ~ l1_struct_0(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_133,c_4019])).

tff(c_4410,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3227,c_4408])).

tff(c_4415,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3228,c_1598,c_4410])).

tff(c_36,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4577,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4415,c_36])).

tff(c_16,plain,(
    ! [A_23,B_24,C_25] :
      ( m1_pre_topc(k1_tsep_1(A_23,B_24,C_25),A_23)
      | ~ m1_pre_topc(C_25,A_23)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc(B_24,A_23)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3235,plain,(
    ! [A_160,B_161,C_162] :
      ( u1_struct_0(k1_tsep_1(A_160,B_161,C_162)) = k2_xboole_0(u1_struct_0(B_161),u1_struct_0(C_162))
      | ~ m1_pre_topc(k1_tsep_1(A_160,B_161,C_162),A_160)
      | ~ v1_pre_topc(k1_tsep_1(A_160,B_161,C_162))
      | v2_struct_0(k1_tsep_1(A_160,B_161,C_162))
      | ~ m1_pre_topc(C_162,A_160)
      | v2_struct_0(C_162)
      | ~ m1_pre_topc(B_161,A_160)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4628,plain,(
    ! [A_186,B_187,C_188] :
      ( u1_struct_0(k1_tsep_1(A_186,B_187,C_188)) = k2_xboole_0(u1_struct_0(B_187),u1_struct_0(C_188))
      | ~ v1_pre_topc(k1_tsep_1(A_186,B_187,C_188))
      | v2_struct_0(k1_tsep_1(A_186,B_187,C_188))
      | ~ m1_pre_topc(C_188,A_186)
      | v2_struct_0(C_188)
      | ~ m1_pre_topc(B_187,A_186)
      | v2_struct_0(B_187)
      | ~ l1_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_16,c_3235])).

tff(c_231,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ v1_xboole_0(k3_xboole_0(A_67,k2_xboole_0(B_68,C_69)))
      | v1_xboole_0(k3_xboole_0(A_67,C_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_28])).

tff(c_14534,plain,(
    ! [A_337,A_338,B_339,C_340] :
      ( ~ v1_xboole_0(k3_xboole_0(A_337,u1_struct_0(k1_tsep_1(A_338,B_339,C_340))))
      | v1_xboole_0(k3_xboole_0(A_337,u1_struct_0(C_340)))
      | ~ v1_pre_topc(k1_tsep_1(A_338,B_339,C_340))
      | v2_struct_0(k1_tsep_1(A_338,B_339,C_340))
      | ~ m1_pre_topc(C_340,A_338)
      | v2_struct_0(C_340)
      | ~ m1_pre_topc(B_339,A_338)
      | v2_struct_0(B_339)
      | ~ l1_pre_topc(A_338)
      | v2_struct_0(A_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4628,c_231])).

tff(c_14581,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4577,c_14534])).

tff(c_14627,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_133,c_14581])).

tff(c_14628,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_14627])).

tff(c_14638,plain,(
    ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14628])).

tff(c_14641,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_14638])).

tff(c_14644,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_14641])).

tff(c_14646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_14644])).

tff(c_14648,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_14628])).

tff(c_20,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ v2_struct_0(k1_tsep_1(A_23,B_24,C_25))
      | ~ m1_pre_topc(C_25,A_23)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc(B_24,A_23)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4776,plain,(
    ! [A_186,B_187,C_188] :
      ( u1_struct_0(k1_tsep_1(A_186,B_187,C_188)) = k2_xboole_0(u1_struct_0(B_187),u1_struct_0(C_188))
      | ~ v1_pre_topc(k1_tsep_1(A_186,B_187,C_188))
      | ~ m1_pre_topc(C_188,A_186)
      | v2_struct_0(C_188)
      | ~ m1_pre_topc(B_187,A_186)
      | v2_struct_0(B_187)
      | ~ l1_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_4628,c_20])).

tff(c_14650,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14648,c_4776])).

tff(c_14653,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_14650])).

tff(c_14654,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_14653])).

tff(c_10,plain,(
    ! [A_18,B_20] :
      ( r1_xboole_0(u1_struct_0(A_18),u1_struct_0(B_20))
      | ~ r1_tsep_1(A_18,B_20)
      | ~ l1_struct_0(B_20)
      | ~ l1_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_17177,plain,(
    ! [B_364,C_365,B_366,A_367] :
      ( r1_xboole_0(k2_xboole_0(u1_struct_0(B_364),u1_struct_0(C_365)),u1_struct_0(B_366))
      | ~ r1_tsep_1(k1_tsep_1(A_367,B_364,C_365),B_366)
      | ~ l1_struct_0(B_366)
      | ~ l1_struct_0(k1_tsep_1(A_367,B_364,C_365))
      | ~ v1_pre_topc(k1_tsep_1(A_367,B_364,C_365))
      | v2_struct_0(k1_tsep_1(A_367,B_364,C_365))
      | ~ m1_pre_topc(C_365,A_367)
      | v2_struct_0(C_365)
      | ~ m1_pre_topc(B_364,A_367)
      | v2_struct_0(B_364)
      | ~ l1_pre_topc(A_367)
      | v2_struct_0(A_367) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4628,c_10])).

tff(c_17179,plain,
    ( r1_xboole_0(k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3227,c_17177])).

tff(c_17182,plain,
    ( r1_xboole_0(u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_14648,c_3228,c_1598,c_14654,c_17179])).

tff(c_17183,plain,
    ( r1_xboole_0(u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_17182])).

tff(c_17370,plain,(
    v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17183])).

tff(c_17373,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_17370,c_20])).

tff(c_17376,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_17373])).

tff(c_17378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_17376])).

tff(c_17380,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_17183])).

tff(c_298,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(u1_struct_0(A_80),u1_struct_0(B_81)) = k1_xboole_0
      | ~ r1_tsep_1(A_80,B_81)
      | ~ l1_struct_0(B_81)
      | ~ l1_struct_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_290,c_12])).

tff(c_17841,plain,(
    ! [A_373,B_374,C_375,A_376] :
      ( k3_xboole_0(u1_struct_0(A_373),k2_xboole_0(u1_struct_0(B_374),u1_struct_0(C_375))) = k1_xboole_0
      | ~ r1_tsep_1(A_373,k1_tsep_1(A_376,B_374,C_375))
      | ~ l1_struct_0(k1_tsep_1(A_376,B_374,C_375))
      | ~ l1_struct_0(A_373)
      | ~ v1_pre_topc(k1_tsep_1(A_376,B_374,C_375))
      | v2_struct_0(k1_tsep_1(A_376,B_374,C_375))
      | ~ m1_pre_topc(C_375,A_376)
      | v2_struct_0(C_375)
      | ~ m1_pre_topc(B_374,A_376)
      | v2_struct_0(B_374)
      | ~ l1_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4628,c_298])).

tff(c_17843,plain,
    ( k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) = k1_xboole_0
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_196,c_17841])).

tff(c_17846,plain,
    ( k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k1_xboole_0
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_14648,c_1598,c_3228,c_14654,c_17843])).

tff(c_17847,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_17380,c_17846])).

tff(c_17379,plain,(
    r1_xboole_0(u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_17183])).

tff(c_17390,plain,(
    k3_xboole_0(u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17379,c_12])).

tff(c_4412,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4')))
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_4408])).

tff(c_4418,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1598,c_3228,c_4412])).

tff(c_4436,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4418,c_36])).

tff(c_299,plain,(
    ! [A_82,B_83,C_84] : k2_xboole_0(k3_xboole_0(A_82,B_83),k3_xboole_0(B_83,C_84)) = k3_xboole_0(B_83,k2_xboole_0(A_82,C_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_334,plain,(
    ! [A_82,B_2,A_1] : k2_xboole_0(k3_xboole_0(A_82,B_2),k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,k2_xboole_0(A_82,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_299])).

tff(c_11646,plain,(
    ! [A_298] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(k1_xboole_0,A_298)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_298,u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4436,c_334])).

tff(c_11741,plain,(
    ! [A_298] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(A_298,u1_struct_0('#skF_4'))))
      | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),A_298)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11646,c_231])).

tff(c_17403,plain,
    ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17390,c_11741])).

tff(c_17503,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_32,c_17403])).

tff(c_4746,plain,(
    ! [A_67,A_186,B_187,C_188] :
      ( ~ v1_xboole_0(k3_xboole_0(A_67,u1_struct_0(k1_tsep_1(A_186,B_187,C_188))))
      | v1_xboole_0(k3_xboole_0(A_67,u1_struct_0(C_188)))
      | ~ v1_pre_topc(k1_tsep_1(A_186,B_187,C_188))
      | v2_struct_0(k1_tsep_1(A_186,B_187,C_188))
      | ~ m1_pre_topc(C_188,A_186)
      | v2_struct_0(C_188)
      | ~ m1_pre_topc(B_187,A_186)
      | v2_struct_0(B_187)
      | ~ l1_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4628,c_231])).

tff(c_17552,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_17503,c_4746])).

tff(c_17578,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_14648,c_17552])).

tff(c_17579,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_17380,c_17578])).

tff(c_17635,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17579,c_36])).

tff(c_34,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k3_xboole_0(A_35,B_36),k3_xboole_0(A_35,C_37)) = k3_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_17718,plain,(
    ! [B_36] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(B_36,u1_struct_0('#skF_3'))) = k2_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),B_36),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_17635,c_34])).

tff(c_19743,plain,(
    ! [B_400] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(B_400,u1_struct_0('#skF_3'))) = k3_xboole_0(u1_struct_0('#skF_4'),B_400) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_17718])).

tff(c_19876,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14654,c_19743])).

tff(c_19961,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17847,c_19876])).

tff(c_14,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_220,plain,(
    ! [A_65,B_66] :
      ( r1_tsep_1(A_65,B_66)
      | ~ r1_xboole_0(u1_struct_0(A_65),u1_struct_0(B_66))
      | ~ l1_struct_0(B_66)
      | ~ l1_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_224,plain,(
    ! [A_65,B_66] :
      ( r1_tsep_1(A_65,B_66)
      | ~ l1_struct_0(B_66)
      | ~ l1_struct_0(A_65)
      | k3_xboole_0(u1_struct_0(A_65),u1_struct_0(B_66)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_220])).

tff(c_20020,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19961,c_224])).

tff(c_20090,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1598,c_20020])).

tff(c_20091,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_686,c_20090])).

tff(c_20113,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_20091])).

tff(c_20117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_20113])).

tff(c_20119,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_200,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_197])).

tff(c_209,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_200])).

tff(c_20118,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_20355,plain,(
    ~ r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20118])).

tff(c_30,plain,(
    ! [B_33,A_32] :
      ( r1_tsep_1(B_33,A_32)
      | ~ r1_tsep_1(A_32,B_33)
      | ~ l1_struct_0(B_33)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_20122,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_20119,c_30])).

tff(c_20123,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20122])).

tff(c_20127,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_20123])).

tff(c_20131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_20127])).

tff(c_20133,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_20122])).

tff(c_21050,plain,(
    ! [A_424,B_425,C_426] :
      ( m1_pre_topc(k1_tsep_1(A_424,B_425,C_426),A_424)
      | ~ m1_pre_topc(C_426,A_424)
      | v2_struct_0(C_426)
      | ~ m1_pre_topc(B_425,A_424)
      | v2_struct_0(B_425)
      | ~ l1_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22731,plain,(
    ! [A_457,B_458,C_459] :
      ( l1_pre_topc(k1_tsep_1(A_457,B_458,C_459))
      | ~ m1_pre_topc(C_459,A_457)
      | v2_struct_0(C_459)
      | ~ m1_pre_topc(B_458,A_457)
      | v2_struct_0(B_458)
      | ~ l1_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_21050,c_24])).

tff(c_21243,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20133,c_219])).

tff(c_21244,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_21243])).

tff(c_21248,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_21244])).

tff(c_22734,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22731,c_21248])).

tff(c_22737,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_22734])).

tff(c_22739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_22737])).

tff(c_22741,plain,(
    l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_21243])).

tff(c_22740,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_21243])).

tff(c_23239,plain,(
    ! [A_471,B_472] :
      ( k3_xboole_0(u1_struct_0(A_471),u1_struct_0(B_472)) = k1_xboole_0
      | ~ r1_tsep_1(A_471,B_472)
      | ~ l1_struct_0(B_472)
      | ~ l1_struct_0(A_471) ) ),
    inference(resolution,[status(thm)],[c_290,c_12])).

tff(c_23280,plain,(
    ! [B_472,A_471] :
      ( k3_xboole_0(u1_struct_0(B_472),u1_struct_0(A_471)) = k1_xboole_0
      | ~ r1_tsep_1(A_471,B_472)
      | ~ l1_struct_0(B_472)
      | ~ l1_struct_0(A_471) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23239,c_2])).

tff(c_23271,plain,(
    ! [A_471,B_472] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k3_xboole_0(u1_struct_0(A_471),k1_xboole_0))
      | ~ r1_tsep_1(A_471,B_472)
      | ~ l1_struct_0(B_472)
      | ~ l1_struct_0(A_471) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23239,c_263])).

tff(c_23308,plain,(
    ! [A_473,B_474] :
      ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(A_473)))
      | ~ r1_tsep_1(A_473,B_474)
      | ~ l1_struct_0(B_474)
      | ~ l1_struct_0(A_473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_133,c_23271])).

tff(c_23316,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4')))
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_23308])).

tff(c_23328,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20133,c_22741,c_23316])).

tff(c_23386,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23328,c_36])).

tff(c_243,plain,(
    ! [A_1,B_2,C_69] : k2_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(B_2,C_69)) = k3_xboole_0(B_2,k2_xboole_0(A_1,C_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_31896,plain,(
    ! [C_579] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(k1_xboole_0,C_579)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),C_579)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23386,c_243])).

tff(c_341,plain,(
    ! [A_85,B_86,B_87] : k2_xboole_0(k3_xboole_0(A_85,B_86),k3_xboole_0(B_87,A_85)) = k3_xboole_0(A_85,k2_xboole_0(B_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_361,plain,(
    ! [A_85,B_86,B_87] :
      ( ~ v1_xboole_0(k3_xboole_0(A_85,k2_xboole_0(B_86,B_87)))
      | v1_xboole_0(k3_xboole_0(B_87,A_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_28])).

tff(c_34484,plain,(
    ! [C_617] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),C_617)))
      | v1_xboole_0(k3_xboole_0(C_617,u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31896,c_361])).

tff(c_34518,plain,(
    ! [A_471] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0))
      | v1_xboole_0(k3_xboole_0(u1_struct_0(A_471),u1_struct_0('#skF_4')))
      | ~ r1_tsep_1(A_471,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0(A_471) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23280,c_34484])).

tff(c_34570,plain,(
    ! [A_618] :
      ( v1_xboole_0(k3_xboole_0(u1_struct_0(A_618),u1_struct_0('#skF_4')))
      | ~ r1_tsep_1(A_618,'#skF_4')
      | ~ l1_struct_0(A_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20133,c_133,c_32,c_34518])).

tff(c_23310,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22740,c_23308])).

tff(c_23319,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22741,c_20133,c_23310])).

tff(c_23559,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23319,c_36])).

tff(c_22748,plain,(
    ! [A_460,B_461,C_462] :
      ( u1_struct_0(k1_tsep_1(A_460,B_461,C_462)) = k2_xboole_0(u1_struct_0(B_461),u1_struct_0(C_462))
      | ~ m1_pre_topc(k1_tsep_1(A_460,B_461,C_462),A_460)
      | ~ v1_pre_topc(k1_tsep_1(A_460,B_461,C_462))
      | v2_struct_0(k1_tsep_1(A_460,B_461,C_462))
      | ~ m1_pre_topc(C_462,A_460)
      | v2_struct_0(C_462)
      | ~ m1_pre_topc(B_461,A_460)
      | v2_struct_0(B_461)
      | ~ l1_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22751,plain,(
    ! [A_23,B_24,C_25] :
      ( u1_struct_0(k1_tsep_1(A_23,B_24,C_25)) = k2_xboole_0(u1_struct_0(B_24),u1_struct_0(C_25))
      | ~ v1_pre_topc(k1_tsep_1(A_23,B_24,C_25))
      | v2_struct_0(k1_tsep_1(A_23,B_24,C_25))
      | ~ m1_pre_topc(C_25,A_23)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc(B_24,A_23)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_16,c_22748])).

tff(c_20132,plain,
    ( ~ l1_struct_0('#skF_2')
    | r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20122])).

tff(c_20134,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20132])).

tff(c_20140,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_20134])).

tff(c_20144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_20140])).

tff(c_20146,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_20132])).

tff(c_20145,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20132])).

tff(c_23312,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20145,c_23308])).

tff(c_23322,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20146,c_20133,c_23312])).

tff(c_23346,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23322,c_36])).

tff(c_240,plain,(
    ! [A_1,B_68,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_68),k3_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,k2_xboole_0(B_68,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_25379,plain,(
    ! [B_498] : k3_xboole_0(k1_xboole_0,k2_xboole_0(u1_struct_0('#skF_2'),B_498)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_498,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23346,c_240])).

tff(c_25482,plain,(
    ! [A_23,C_25] :
      ( k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1(A_23,'#skF_2',C_25))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0(C_25),k1_xboole_0))
      | ~ v1_pre_topc(k1_tsep_1(A_23,'#skF_2',C_25))
      | v2_struct_0(k1_tsep_1(A_23,'#skF_2',C_25))
      | ~ m1_pre_topc(C_25,A_23)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc('#skF_2',A_23)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22751,c_25379])).

tff(c_25551,plain,(
    ! [A_23,C_25] :
      ( k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1(A_23,'#skF_2',C_25))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(C_25)))
      | ~ v1_pre_topc(k1_tsep_1(A_23,'#skF_2',C_25))
      | v2_struct_0(k1_tsep_1(A_23,'#skF_2',C_25))
      | ~ m1_pre_topc(C_25,A_23)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc('#skF_2',A_23)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_25482])).

tff(c_26992,plain,(
    ! [A_515,C_516] :
      ( k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1(A_515,'#skF_2',C_516))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(C_516)))
      | ~ v1_pre_topc(k1_tsep_1(A_515,'#skF_2',C_516))
      | v2_struct_0(k1_tsep_1(A_515,'#skF_2',C_516))
      | ~ m1_pre_topc(C_516,A_515)
      | v2_struct_0(C_516)
      | ~ m1_pre_topc('#skF_2',A_515)
      | ~ l1_pre_topc(A_515)
      | v2_struct_0(A_515) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_25551])).

tff(c_27059,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3'))) = k1_xboole_0
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23559,c_26992])).

tff(c_27082,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3'))) = k1_xboole_0
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_27059])).

tff(c_27083,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3'))) = k1_xboole_0
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_44,c_27082])).

tff(c_27231,plain,(
    ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_27083])).

tff(c_27234,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_27231])).

tff(c_27237,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_27234])).

tff(c_27239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_27237])).

tff(c_27241,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_27083])).

tff(c_24487,plain,(
    ! [A_484,B_485,C_486] :
      ( u1_struct_0(k1_tsep_1(A_484,B_485,C_486)) = k2_xboole_0(u1_struct_0(B_485),u1_struct_0(C_486))
      | ~ v1_pre_topc(k1_tsep_1(A_484,B_485,C_486))
      | v2_struct_0(k1_tsep_1(A_484,B_485,C_486))
      | ~ m1_pre_topc(C_486,A_484)
      | v2_struct_0(C_486)
      | ~ m1_pre_topc(B_485,A_484)
      | v2_struct_0(B_485)
      | ~ l1_pre_topc(A_484)
      | v2_struct_0(A_484) ) ),
    inference(resolution,[status(thm)],[c_16,c_22748])).

tff(c_34165,plain,(
    ! [A_597,B_598,C_599] :
      ( u1_struct_0(k1_tsep_1(A_597,B_598,C_599)) = k2_xboole_0(u1_struct_0(B_598),u1_struct_0(C_599))
      | ~ v1_pre_topc(k1_tsep_1(A_597,B_598,C_599))
      | ~ m1_pre_topc(C_599,A_597)
      | v2_struct_0(C_599)
      | ~ m1_pre_topc(B_598,A_597)
      | v2_struct_0(B_598)
      | ~ l1_pre_topc(A_597)
      | v2_struct_0(A_597) ) ),
    inference(resolution,[status(thm)],[c_24487,c_20])).

tff(c_34167,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_27241,c_34165])).

tff(c_34172,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_34167])).

tff(c_34173,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_34172])).

tff(c_628,plain,(
    ! [A_92,B_93,B_94] :
      ( ~ v1_xboole_0(k3_xboole_0(A_92,k2_xboole_0(B_93,B_94)))
      | v1_xboole_0(k3_xboole_0(B_94,A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_28])).

tff(c_650,plain,(
    ! [B_93,B_94,A_1] :
      ( ~ v1_xboole_0(k3_xboole_0(k2_xboole_0(B_93,B_94),A_1))
      | v1_xboole_0(k3_xboole_0(B_94,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_628])).

tff(c_34216,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')),A_1))
      | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'),A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34173,c_650])).

tff(c_34574,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))
    | ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34570,c_34216])).

tff(c_34602,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22741,c_22740,c_2,c_34574])).

tff(c_34640,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34602,c_36])).

tff(c_34680,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34640,c_224])).

tff(c_34743,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20133,c_34680])).

tff(c_34744,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_20355,c_34743])).

tff(c_34765,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_34744])).

tff(c_34769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_34765])).

tff(c_34771,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20118])).

tff(c_34773,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34771,c_30])).

tff(c_34776,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20133,c_34773])).

tff(c_34777,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34776])).

tff(c_34780,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_34777])).

tff(c_34784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_34780])).

tff(c_34785,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34776])).

tff(c_126,plain,
    ( ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_35440,plain,(
    ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20119,c_34771,c_196,c_20145,c_34785,c_126])).

tff(c_35495,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20133,c_219])).

tff(c_35496,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_35440,c_35495])).

tff(c_35500,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_35496])).

tff(c_36857,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36854,c_35500])).

tff(c_36860,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_36857])).

tff(c_36862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_36860])).

tff(c_36864,plain,(
    ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_70,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_2')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_36884,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36864,c_70])).

tff(c_36885,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36884])).

tff(c_36886,plain,(
    ! [B_676,A_677] :
      ( r1_tsep_1(B_676,A_677)
      | ~ r1_tsep_1(A_677,B_676)
      | ~ l1_struct_0(B_676)
      | ~ l1_struct_0(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36889,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36885,c_36886])).

tff(c_36890,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36889])).

tff(c_36898,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_36890])).

tff(c_36902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36880,c_36898])).

tff(c_36904,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_36889])).

tff(c_36868,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_36865])).

tff(c_36877,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36868])).

tff(c_37792,plain,(
    ! [A_727,B_728,C_729] :
      ( m1_pre_topc(k1_tsep_1(A_727,B_728,C_729),A_727)
      | ~ m1_pre_topc(C_729,A_727)
      | v2_struct_0(C_729)
      | ~ m1_pre_topc(B_728,A_727)
      | v2_struct_0(B_728)
      | ~ l1_pre_topc(A_727)
      | v2_struct_0(A_727) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_37796,plain,(
    ! [A_727,B_728,C_729] :
      ( l1_pre_topc(k1_tsep_1(A_727,B_728,C_729))
      | ~ m1_pre_topc(C_729,A_727)
      | v2_struct_0(C_729)
      | ~ m1_pre_topc(B_728,A_727)
      | v2_struct_0(B_728)
      | ~ l1_pre_topc(A_727)
      | v2_struct_0(A_727) ) ),
    inference(resolution,[status(thm)],[c_37792,c_24])).

tff(c_36903,plain,
    ( ~ l1_struct_0('#skF_2')
    | r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36889])).

tff(c_36905,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36903])).

tff(c_36910,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_36905])).

tff(c_36914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36883,c_36910])).

tff(c_36916,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_36903])).

tff(c_36922,plain,(
    ! [A_680,B_681] :
      ( r1_xboole_0(u1_struct_0(A_680),u1_struct_0(B_681))
      | ~ r1_tsep_1(A_680,B_681)
      | ~ l1_struct_0(B_681)
      | ~ l1_struct_0(A_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38494,plain,(
    ! [A_749,B_750] :
      ( k3_xboole_0(u1_struct_0(A_749),u1_struct_0(B_750)) = k1_xboole_0
      | ~ r1_tsep_1(A_749,B_750)
      | ~ l1_struct_0(B_750)
      | ~ l1_struct_0(A_749) ) ),
    inference(resolution,[status(thm)],[c_36922,c_12])).

tff(c_38544,plain,(
    ! [B_750,A_749] :
      ( k3_xboole_0(u1_struct_0(B_750),u1_struct_0(A_749)) = k1_xboole_0
      | ~ r1_tsep_1(A_749,B_750)
      | ~ l1_struct_0(B_750)
      | ~ l1_struct_0(A_749) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_38494])).

tff(c_36863,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_36927,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36863])).

tff(c_36929,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36927,c_30])).

tff(c_36932,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36904,c_36929])).

tff(c_36933,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36932])).

tff(c_36936,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_36933])).

tff(c_36940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36877,c_36936])).

tff(c_36942,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_36932])).

tff(c_36941,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36932])).

tff(c_36959,plain,(
    ! [A_684,B_685,C_686] : k2_xboole_0(k3_xboole_0(A_684,B_685),k3_xboole_0(A_684,C_686)) = k3_xboole_0(A_684,k2_xboole_0(B_685,C_686)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36983,plain,(
    ! [A_687,B_688,C_689] :
      ( ~ v1_xboole_0(k3_xboole_0(A_687,k2_xboole_0(B_688,C_689)))
      | v1_xboole_0(k3_xboole_0(A_687,C_689)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36959,c_28])).

tff(c_36997,plain,(
    ! [A_687,A_34] :
      ( ~ v1_xboole_0(k3_xboole_0(A_687,A_34))
      | v1_xboole_0(k3_xboole_0(A_687,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_36983])).

tff(c_38523,plain,(
    ! [A_749,B_750] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k3_xboole_0(u1_struct_0(A_749),k1_xboole_0))
      | ~ r1_tsep_1(A_749,B_750)
      | ~ l1_struct_0(B_750)
      | ~ l1_struct_0(A_749) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38494,c_36997])).

tff(c_38794,plain,(
    ! [A_754,B_755] :
      ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(A_754)))
      | ~ r1_tsep_1(A_754,B_755)
      | ~ l1_struct_0(B_755)
      | ~ l1_struct_0(A_754) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_133,c_38523])).

tff(c_38796,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36941,c_38794])).

tff(c_38805,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36904,c_36942,c_38796])).

tff(c_38832,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38805,c_36])).

tff(c_37028,plain,(
    ! [A_697,B_698,B_699] : k2_xboole_0(k3_xboole_0(A_697,B_698),k3_xboole_0(B_699,A_697)) = k3_xboole_0(A_697,k2_xboole_0(B_698,B_699)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_36959])).

tff(c_37060,plain,(
    ! [A_1,B_2,B_699] : k2_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(B_699,B_2)) = k3_xboole_0(B_2,k2_xboole_0(A_1,B_699)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_37028])).

tff(c_47895,plain,(
    ! [B_874] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(k1_xboole_0,B_874)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_874,u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_38832,c_37060])).

tff(c_36965,plain,(
    ! [A_684,B_685,C_686] :
      ( ~ v1_xboole_0(k3_xboole_0(A_684,k2_xboole_0(B_685,C_686)))
      | v1_xboole_0(k3_xboole_0(A_684,C_686)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36959,c_28])).

tff(c_50374,plain,(
    ! [B_914] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(B_914,u1_struct_0('#skF_4'))))
      | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),B_914)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47895,c_36965])).

tff(c_50382,plain,(
    ! [B_750] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0))
      | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(B_750)))
      | ~ r1_tsep_1('#skF_4',B_750)
      | ~ l1_struct_0(B_750)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38544,c_50374])).

tff(c_50416,plain,(
    ! [B_915] :
      ( v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(B_915)))
      | ~ r1_tsep_1('#skF_4',B_915)
      | ~ l1_struct_0(B_915) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36904,c_133,c_32,c_50382])).

tff(c_51225,plain,(
    ! [B_935] :
      ( v1_xboole_0(k3_xboole_0(u1_struct_0(B_935),u1_struct_0('#skF_4')))
      | ~ r1_tsep_1('#skF_4',B_935)
      | ~ l1_struct_0(B_935) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_50416])).

tff(c_51262,plain,(
    ! [B_935] :
      ( k3_xboole_0(u1_struct_0(B_935),u1_struct_0('#skF_4')) = k1_xboole_0
      | ~ r1_tsep_1('#skF_4',B_935)
      | ~ l1_struct_0(B_935) ) ),
    inference(resolution,[status(thm)],[c_51225,c_36])).

tff(c_36915,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36903])).

tff(c_38800,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36915,c_38794])).

tff(c_38811,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36916,c_36904,c_38800])).

tff(c_39005,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38811,c_36])).

tff(c_48444,plain,(
    ! [B_879] : k3_xboole_0(u1_struct_0('#skF_2'),k2_xboole_0(k1_xboole_0,B_879)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_879,u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_39005,c_37060])).

tff(c_36977,plain,(
    ! [A_1,B_2,C_686] : k2_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(B_2,C_686)) = k3_xboole_0(B_2,k2_xboole_0(A_1,C_686)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_36959])).

tff(c_39067,plain,(
    ! [C_686] : k3_xboole_0(u1_struct_0('#skF_2'),k2_xboole_0(k1_xboole_0,C_686)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_2'),C_686)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39005,c_36977])).

tff(c_56634,plain,(
    ! [B_1020] : k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_2'),B_1020)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_1020,u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_48444,c_39067])).

tff(c_56779,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_51262,c_56634])).

tff(c_56861,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36916,c_36885,c_32,c_56779])).

tff(c_56923,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_56861,c_28])).

tff(c_56947,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_56923])).

tff(c_56988,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56947,c_36])).

tff(c_36974,plain,(
    ! [A_1,B_685,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_685),k3_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,k2_xboole_0(B_685,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_36959])).

tff(c_57066,plain,(
    ! [B_685] : k3_xboole_0(u1_struct_0('#skF_2'),k2_xboole_0(B_685,u1_struct_0('#skF_4'))) = k2_xboole_0(k3_xboole_0(u1_struct_0('#skF_2'),B_685),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56988,c_36974])).

tff(c_59391,plain,(
    ! [B_1041] : k3_xboole_0(u1_struct_0('#skF_2'),k2_xboole_0(B_1041,u1_struct_0('#skF_4'))) = k3_xboole_0(u1_struct_0('#skF_2'),B_1041) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_57066])).

tff(c_38516,plain,(
    ! [A_749,B_750,B_2] :
      ( k3_xboole_0(u1_struct_0(A_749),k2_xboole_0(u1_struct_0(B_750),B_2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_2,u1_struct_0(A_749)))
      | ~ r1_tsep_1(A_749,B_750)
      | ~ l1_struct_0(B_750)
      | ~ l1_struct_0(A_749) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38494,c_36974])).

tff(c_59420,plain,(
    ! [B_750] :
      ( k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0(B_750)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))
      | ~ r1_tsep_1('#skF_2',B_750)
      | ~ l1_struct_0(B_750)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59391,c_38516])).

tff(c_59585,plain,(
    ! [B_750] :
      ( k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0(B_750)) = k1_xboole_0
      | ~ r1_tsep_1('#skF_2',B_750)
      | ~ l1_struct_0(B_750) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36916,c_32,c_56988,c_59420])).

tff(c_36926,plain,(
    ! [A_680,B_681] :
      ( k3_xboole_0(u1_struct_0(A_680),u1_struct_0(B_681)) = k1_xboole_0
      | ~ r1_tsep_1(A_680,B_681)
      | ~ l1_struct_0(B_681)
      | ~ l1_struct_0(A_680) ) ),
    inference(resolution,[status(thm)],[c_36922,c_12])).

tff(c_50389,plain,(
    ! [A_680] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0))
      | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(A_680)))
      | ~ r1_tsep_1(A_680,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0(A_680) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36926,c_50374])).

tff(c_50726,plain,(
    ! [A_924] :
      ( v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(A_924)))
      | ~ r1_tsep_1(A_924,'#skF_4')
      | ~ l1_struct_0(A_924) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36904,c_133,c_32,c_50389])).

tff(c_51313,plain,(
    ! [A_937] :
      ( k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(A_937)) = k1_xboole_0
      | ~ r1_tsep_1(A_937,'#skF_4')
      | ~ l1_struct_0(A_937) ) ),
    inference(resolution,[status(thm)],[c_50726,c_36])).

tff(c_51502,plain,(
    ! [A_943] :
      ( k3_xboole_0(u1_struct_0(A_943),u1_struct_0('#skF_4')) = k1_xboole_0
      | ~ r1_tsep_1(A_943,'#skF_4')
      | ~ l1_struct_0(A_943) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_51313])).

tff(c_38798,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36927,c_38794])).

tff(c_38808,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36942,c_36904,c_38798])).

tff(c_38934,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38808,c_36])).

tff(c_38941,plain,(
    ! [B_699] : k3_xboole_0(u1_struct_0('#skF_3'),k2_xboole_0(k1_xboole_0,B_699)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_699,u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_38934,c_37060])).

tff(c_48275,plain,(
    ! [C_878] : k3_xboole_0(u1_struct_0('#skF_3'),k2_xboole_0(k1_xboole_0,C_878)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_3'),C_878)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38934,c_36977])).

tff(c_48385,plain,(
    ! [B_699] : k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_3'),B_699)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_699,u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_38941,c_48275])).

tff(c_51534,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_51502,c_48385])).

tff(c_51648,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36942,c_36927,c_32,c_51534])).

tff(c_51739,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_51648,c_28])).

tff(c_51763,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_51739])).

tff(c_51805,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51763,c_36])).

tff(c_51872,plain,(
    ! [A_1] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(A_1,u1_struct_0('#skF_3'))) = k2_xboole_0(k3_xboole_0(A_1,u1_struct_0('#skF_4')),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_51805,c_36977])).

tff(c_51940,plain,(
    ! [A_1] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(A_1,u1_struct_0('#skF_3'))) = k3_xboole_0(A_1,u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_51872])).

tff(c_38307,plain,(
    ! [A_743,B_744,C_745] :
      ( u1_struct_0(k1_tsep_1(A_743,B_744,C_745)) = k2_xboole_0(u1_struct_0(B_744),u1_struct_0(C_745))
      | ~ m1_pre_topc(k1_tsep_1(A_743,B_744,C_745),A_743)
      | ~ v1_pre_topc(k1_tsep_1(A_743,B_744,C_745))
      | v2_struct_0(k1_tsep_1(A_743,B_744,C_745))
      | ~ m1_pre_topc(C_745,A_743)
      | v2_struct_0(C_745)
      | ~ m1_pre_topc(B_744,A_743)
      | v2_struct_0(B_744)
      | ~ l1_pre_topc(A_743)
      | v2_struct_0(A_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40384,plain,(
    ! [A_770,B_771,C_772] :
      ( u1_struct_0(k1_tsep_1(A_770,B_771,C_772)) = k2_xboole_0(u1_struct_0(B_771),u1_struct_0(C_772))
      | ~ v1_pre_topc(k1_tsep_1(A_770,B_771,C_772))
      | v2_struct_0(k1_tsep_1(A_770,B_771,C_772))
      | ~ m1_pre_topc(C_772,A_770)
      | v2_struct_0(C_772)
      | ~ m1_pre_topc(B_771,A_770)
      | v2_struct_0(B_771)
      | ~ l1_pre_topc(A_770)
      | v2_struct_0(A_770) ) ),
    inference(resolution,[status(thm)],[c_16,c_38307])).

tff(c_36950,plain,(
    ! [A_682,B_683] :
      ( r1_tsep_1(A_682,B_683)
      | ~ r1_xboole_0(u1_struct_0(A_682),u1_struct_0(B_683))
      | ~ l1_struct_0(B_683)
      | ~ l1_struct_0(A_682) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36958,plain,(
    ! [A_682,B_683] :
      ( r1_tsep_1(A_682,B_683)
      | ~ l1_struct_0(B_683)
      | ~ l1_struct_0(A_682)
      | k3_xboole_0(u1_struct_0(A_682),u1_struct_0(B_683)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_36950])).

tff(c_53490,plain,(
    ! [A_969,A_970,B_971,C_972] :
      ( r1_tsep_1(A_969,k1_tsep_1(A_970,B_971,C_972))
      | ~ l1_struct_0(k1_tsep_1(A_970,B_971,C_972))
      | ~ l1_struct_0(A_969)
      | k3_xboole_0(u1_struct_0(A_969),k2_xboole_0(u1_struct_0(B_971),u1_struct_0(C_972))) != k1_xboole_0
      | ~ v1_pre_topc(k1_tsep_1(A_970,B_971,C_972))
      | v2_struct_0(k1_tsep_1(A_970,B_971,C_972))
      | ~ m1_pre_topc(C_972,A_970)
      | v2_struct_0(C_972)
      | ~ m1_pre_topc(B_971,A_970)
      | v2_struct_0(B_971)
      | ~ l1_pre_topc(A_970)
      | v2_struct_0(A_970) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40384,c_36958])).

tff(c_53496,plain,(
    ! [A_970,B_971] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_970,B_971,'#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_970,B_971,'#skF_3'))
      | ~ l1_struct_0('#skF_4')
      | k3_xboole_0(u1_struct_0(B_971),u1_struct_0('#skF_4')) != k1_xboole_0
      | ~ v1_pre_topc(k1_tsep_1(A_970,B_971,'#skF_3'))
      | v2_struct_0(k1_tsep_1(A_970,B_971,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_970)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_971,A_970)
      | v2_struct_0(B_971)
      | ~ l1_pre_topc(A_970)
      | v2_struct_0(A_970) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51940,c_53490])).

tff(c_53542,plain,(
    ! [A_970,B_971] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_970,B_971,'#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_970,B_971,'#skF_3'))
      | k3_xboole_0(u1_struct_0(B_971),u1_struct_0('#skF_4')) != k1_xboole_0
      | ~ v1_pre_topc(k1_tsep_1(A_970,B_971,'#skF_3'))
      | v2_struct_0(k1_tsep_1(A_970,B_971,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_970)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_971,A_970)
      | v2_struct_0(B_971)
      | ~ l1_pre_topc(A_970)
      | v2_struct_0(A_970) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36904,c_53496])).

tff(c_61809,plain,(
    ! [A_1056,B_1057] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_1056,B_1057,'#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_1056,B_1057,'#skF_3'))
      | k3_xboole_0(u1_struct_0(B_1057),u1_struct_0('#skF_4')) != k1_xboole_0
      | ~ v1_pre_topc(k1_tsep_1(A_1056,B_1057,'#skF_3'))
      | v2_struct_0(k1_tsep_1(A_1056,B_1057,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_1056)
      | ~ m1_pre_topc(B_1057,A_1056)
      | v2_struct_0(B_1057)
      | ~ l1_pre_topc(A_1056)
      | v2_struct_0(A_1056) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_53542])).

tff(c_61812,plain,(
    ! [A_1056] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_1056,'#skF_2','#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_1056,'#skF_2','#skF_3'))
      | ~ v1_pre_topc(k1_tsep_1(A_1056,'#skF_2','#skF_3'))
      | v2_struct_0(k1_tsep_1(A_1056,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_1056)
      | ~ m1_pre_topc('#skF_2',A_1056)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1056)
      | v2_struct_0(A_1056)
      | ~ r1_tsep_1('#skF_2','#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59585,c_61809])).

tff(c_61858,plain,(
    ! [A_1056] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_1056,'#skF_2','#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_1056,'#skF_2','#skF_3'))
      | ~ v1_pre_topc(k1_tsep_1(A_1056,'#skF_2','#skF_3'))
      | v2_struct_0(k1_tsep_1(A_1056,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_1056)
      | ~ m1_pre_topc('#skF_2',A_1056)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1056)
      | v2_struct_0(A_1056) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36904,c_36915,c_61812])).

tff(c_62971,plain,(
    ! [A_1061] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_1061,'#skF_2','#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_1061,'#skF_2','#skF_3'))
      | ~ v1_pre_topc(k1_tsep_1(A_1061,'#skF_2','#skF_3'))
      | v2_struct_0(k1_tsep_1(A_1061,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_1061)
      | ~ m1_pre_topc('#skF_2',A_1061)
      | ~ l1_pre_topc(A_1061)
      | v2_struct_0(A_1061) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_61858])).

tff(c_62988,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62971,c_36864])).

tff(c_63012,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_62988])).

tff(c_63013,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_63012])).

tff(c_65704,plain,(
    ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_63013])).

tff(c_65707,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_65704])).

tff(c_65710,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_65707])).

tff(c_65712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_65710])).

tff(c_65714,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_63013])).

tff(c_40558,plain,(
    ! [A_770,B_771,C_772] :
      ( u1_struct_0(k1_tsep_1(A_770,B_771,C_772)) = k2_xboole_0(u1_struct_0(B_771),u1_struct_0(C_772))
      | ~ v1_pre_topc(k1_tsep_1(A_770,B_771,C_772))
      | ~ m1_pre_topc(C_772,A_770)
      | v2_struct_0(C_772)
      | ~ m1_pre_topc(B_771,A_770)
      | v2_struct_0(B_771)
      | ~ l1_pre_topc(A_770)
      | v2_struct_0(A_770) ) ),
    inference(resolution,[status(thm)],[c_40384,c_20])).

tff(c_65716,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_65714,c_40558])).

tff(c_65719,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_65716])).

tff(c_65720,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_65719])).

tff(c_51892,plain,(
    ! [B_36] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(B_36,u1_struct_0('#skF_3'))) = k2_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),B_36),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_51805,c_34])).

tff(c_51950,plain,(
    ! [B_36] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(B_36,u1_struct_0('#skF_3'))) = k3_xboole_0(u1_struct_0('#skF_4'),B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_51892])).

tff(c_65749,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_65720,c_51950])).

tff(c_65819,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56988,c_65749])).

tff(c_66432,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_65819,c_36958])).

tff(c_66509,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36904,c_66432])).

tff(c_66510,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36864,c_66509])).

tff(c_66535,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_66510])).

tff(c_66554,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_37796,c_66535])).

tff(c_66557,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_66554])).

tff(c_66559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_66557])).

tff(c_66561,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36863])).

tff(c_66560,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36863])).

tff(c_66562,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66560])).

tff(c_66564,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66562,c_30])).

tff(c_66567,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36904,c_66564])).

tff(c_66568,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66561,c_66567])).

tff(c_66571,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_66568])).

tff(c_66575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36877,c_66571])).

tff(c_66576,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_66560])).

tff(c_66579,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66576,c_30])).

tff(c_66582,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36904,c_66579])).

tff(c_66583,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36864,c_66582])).

tff(c_66587,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_66583])).

tff(c_69105,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_69102,c_66587])).

tff(c_69108,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_69105])).

tff(c_69110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_69108])).

tff(c_69112,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36884])).

tff(c_69973,plain,(
    ! [A_1216,B_1217,C_1218] :
      ( m1_pre_topc(k1_tsep_1(A_1216,B_1217,C_1218),A_1216)
      | ~ m1_pre_topc(C_1218,A_1216)
      | v2_struct_0(C_1218)
      | ~ m1_pre_topc(B_1217,A_1216)
      | v2_struct_0(B_1217)
      | ~ l1_pre_topc(A_1216)
      | v2_struct_0(A_1216) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_71369,plain,(
    ! [A_1252,B_1253,C_1254] :
      ( l1_pre_topc(k1_tsep_1(A_1252,B_1253,C_1254))
      | ~ m1_pre_topc(C_1254,A_1252)
      | v2_struct_0(C_1254)
      | ~ m1_pre_topc(B_1253,A_1252)
      | v2_struct_0(B_1253)
      | ~ l1_pre_topc(A_1252)
      | v2_struct_0(A_1252) ) ),
    inference(resolution,[status(thm)],[c_69973,c_24])).

tff(c_68,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_2')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_69113,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36864,c_69112,c_68])).

tff(c_69114,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_69113])).

tff(c_69116,plain,(
    ! [B_1167,A_1168] :
      ( r1_tsep_1(B_1167,A_1168)
      | ~ r1_tsep_1(A_1168,B_1167)
      | ~ l1_struct_0(B_1167)
      | ~ l1_struct_0(A_1168) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_69118,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_69114,c_69116])).

tff(c_69121,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36864,c_69118])).

tff(c_69122,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_69121])).

tff(c_69126,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_69122])).

tff(c_71372,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_71369,c_69126])).

tff(c_71375,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_71372])).

tff(c_71377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_71375])).

tff(c_71378,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_69121])).

tff(c_71382,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_71378])).

tff(c_71386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36880,c_71382])).

tff(c_71388,plain,(
    ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_69113])).

tff(c_69111,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36884])).

tff(c_71391,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_71388,c_69111])).

tff(c_71392,plain,(
    ! [B_1255,A_1256] :
      ( r1_tsep_1(B_1255,A_1256)
      | ~ r1_tsep_1(A_1256,B_1255)
      | ~ l1_struct_0(B_1255)
      | ~ l1_struct_0(A_1256) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_71394,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_71391,c_71392])).

tff(c_71401,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_69112,c_71394])).

tff(c_71406,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_71401])).

tff(c_71409,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_71406])).

tff(c_71413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36883,c_71409])).

tff(c_71414,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_71401])).

tff(c_71420,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_71414])).

tff(c_71424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36880,c_71420])).

%------------------------------------------------------------------------------
