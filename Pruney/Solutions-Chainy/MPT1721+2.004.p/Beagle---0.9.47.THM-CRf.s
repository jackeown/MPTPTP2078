%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:44 EST 2020

% Result     : Theorem 16.46s
% Output     : CNFRefutation 16.49s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 340 expanded)
%              Number of leaves         :   29 ( 147 expanded)
%              Depth                    :   24
%              Number of atoms          :  351 (2040 expanded)
%              Number of equality atoms :   20 (  70 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > k2_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_203,negated_conjecture,(
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

tff(f_86,axiom,(
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

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k2_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tmap_1)).

tff(f_155,axiom,(
    ! [A] :
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
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(B,D)
                          & m1_pre_topc(C,E) )
                       => ( r1_tsep_1(B,C)
                          | m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,D,E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
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

tff(f_169,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_32,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_46,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_14,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_pre_topc(k2_tsep_1(A_20,B_21,C_22),A_20)
      | ~ m1_pre_topc(C_22,A_20)
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,A_20)
      | v2_struct_0(B_21)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_352,plain,(
    ! [A_107,B_108] :
      ( k1_tsep_1(A_107,B_108,B_108) = g1_pre_topc(u1_struct_0(B_108),u1_pre_topc(B_108))
      | ~ m1_pre_topc(B_108,A_107)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_360,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k1_tsep_1('#skF_1','#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_352])).

tff(c_377,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k1_tsep_1('#skF_1','#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_360])).

tff(c_378,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k1_tsep_1('#skF_1','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40,c_377])).

tff(c_403,plain,(
    ! [A_109,B_110] :
      ( k2_tsep_1(A_109,B_110,B_110) = g1_pre_topc(u1_struct_0(B_110),u1_pre_topc(B_110))
      | ~ m1_pre_topc(B_110,A_109)
      | v2_struct_0(B_110)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_411,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k2_tsep_1('#skF_1','#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_403])).

tff(c_431,plain,
    ( k2_tsep_1('#skF_1','#skF_4','#skF_4') = k1_tsep_1('#skF_1','#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_378,c_411])).

tff(c_432,plain,(
    k2_tsep_1('#skF_1','#skF_4','#skF_4') = k1_tsep_1('#skF_1','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40,c_431])).

tff(c_23909,plain,(
    ! [B_660,E_662,C_658,A_659,D_661] :
      ( m1_pre_topc(k2_tsep_1(A_659,B_660,C_658),k2_tsep_1(A_659,D_661,E_662))
      | r1_tsep_1(B_660,C_658)
      | ~ m1_pre_topc(C_658,E_662)
      | ~ m1_pre_topc(B_660,D_661)
      | ~ m1_pre_topc(E_662,A_659)
      | v2_struct_0(E_662)
      | ~ m1_pre_topc(D_661,A_659)
      | v2_struct_0(D_661)
      | ~ m1_pre_topc(C_658,A_659)
      | v2_struct_0(C_658)
      | ~ m1_pre_topc(B_660,A_659)
      | v2_struct_0(B_660)
      | ~ l1_pre_topc(A_659)
      | ~ v2_pre_topc(A_659)
      | v2_struct_0(A_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_23935,plain,(
    ! [B_660,C_658] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_660,C_658),k1_tsep_1('#skF_1','#skF_4','#skF_4'))
      | r1_tsep_1(B_660,C_658)
      | ~ m1_pre_topc(C_658,'#skF_4')
      | ~ m1_pre_topc(B_660,'#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_658,'#skF_1')
      | v2_struct_0(C_658)
      | ~ m1_pre_topc(B_660,'#skF_1')
      | v2_struct_0(B_660)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_23909])).

tff(c_23956,plain,(
    ! [B_660,C_658] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_660,C_658),k1_tsep_1('#skF_1','#skF_4','#skF_4'))
      | r1_tsep_1(B_660,C_658)
      | ~ m1_pre_topc(C_658,'#skF_4')
      | ~ m1_pre_topc(B_660,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_658,'#skF_1')
      | v2_struct_0(C_658)
      | ~ m1_pre_topc(B_660,'#skF_1')
      | v2_struct_0(B_660)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_38,c_38,c_23935])).

tff(c_23957,plain,(
    ! [B_660,C_658] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_660,C_658),k1_tsep_1('#skF_1','#skF_4','#skF_4'))
      | r1_tsep_1(B_660,C_658)
      | ~ m1_pre_topc(C_658,'#skF_4')
      | ~ m1_pre_topc(B_660,'#skF_4')
      | ~ m1_pre_topc(C_658,'#skF_1')
      | v2_struct_0(C_658)
      | ~ m1_pre_topc(B_660,'#skF_1')
      | v2_struct_0(B_660) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40,c_23956])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ v2_struct_0(k2_tsep_1(A_20,B_21,C_22))
      | ~ m1_pre_topc(C_22,A_20)
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,A_20)
      | v2_struct_0(B_21)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_453,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_18])).

tff(c_460,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_38,c_453])).

tff(c_461,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40,c_460])).

tff(c_16,plain,(
    ! [A_20,B_21,C_22] :
      ( v1_pre_topc(k2_tsep_1(A_20,B_21,C_22))
      | ~ m1_pre_topc(C_22,A_20)
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,A_20)
      | v2_struct_0(B_21)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_450,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_16])).

tff(c_457,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_38,c_450])).

tff(c_458,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40,c_457])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_79,B_80] :
      ( k2_xboole_0(A_79,B_80) = B_80
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_463,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_pre_topc(k2_tsep_1(A_111,B_112,C_113),A_111)
      | ~ m1_pre_topc(C_113,A_111)
      | v2_struct_0(C_113)
      | ~ m1_pre_topc(B_112,A_111)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_474,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_4'),'#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_463])).

tff(c_480,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_38,c_474])).

tff(c_481,plain,(
    m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40,c_480])).

tff(c_11234,plain,(
    ! [A_374,B_375,C_376] :
      ( u1_struct_0(k1_tsep_1(A_374,B_375,C_376)) = k2_xboole_0(u1_struct_0(B_375),u1_struct_0(C_376))
      | ~ m1_pre_topc(k1_tsep_1(A_374,B_375,C_376),A_374)
      | ~ v1_pre_topc(k1_tsep_1(A_374,B_375,C_376))
      | v2_struct_0(k1_tsep_1(A_374,B_375,C_376))
      | ~ m1_pre_topc(C_376,A_374)
      | v2_struct_0(C_376)
      | ~ m1_pre_topc(B_375,A_374)
      | v2_struct_0(B_375)
      | ~ l1_pre_topc(A_374)
      | v2_struct_0(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_11240,plain,
    ( k2_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_4'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_481,c_11234])).

tff(c_11251,plain,
    ( u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_4')) = u1_struct_0('#skF_4')
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_458,c_61,c_11240])).

tff(c_11252,plain,(
    u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_4')) = u1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40,c_461,c_11251])).

tff(c_26,plain,(
    ! [B_64,C_66,A_60] :
      ( r1_tarski(u1_struct_0(B_64),u1_struct_0(C_66))
      | ~ m1_pre_topc(B_64,C_66)
      | ~ m1_pre_topc(C_66,A_60)
      | ~ m1_pre_topc(B_64,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_30551,plain,(
    ! [B_801,A_802,B_803,C_804] :
      ( r1_tarski(u1_struct_0(B_801),u1_struct_0(k2_tsep_1(A_802,B_803,C_804)))
      | ~ m1_pre_topc(B_801,k2_tsep_1(A_802,B_803,C_804))
      | ~ m1_pre_topc(B_801,A_802)
      | ~ v2_pre_topc(A_802)
      | ~ m1_pre_topc(C_804,A_802)
      | v2_struct_0(C_804)
      | ~ m1_pre_topc(B_803,A_802)
      | v2_struct_0(B_803)
      | ~ l1_pre_topc(A_802)
      | v2_struct_0(A_802) ) ),
    inference(resolution,[status(thm)],[c_463,c_26])).

tff(c_30588,plain,(
    ! [B_801] :
      ( r1_tarski(u1_struct_0(B_801),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_4')))
      | ~ m1_pre_topc(B_801,k2_tsep_1('#skF_1','#skF_4','#skF_4'))
      | ~ m1_pre_topc(B_801,'#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_30551])).

tff(c_30602,plain,(
    ! [B_801] :
      ( r1_tarski(u1_struct_0(B_801),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_801,k1_tsep_1('#skF_1','#skF_4','#skF_4'))
      | ~ m1_pre_topc(B_801,'#skF_1')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_38,c_52,c_432,c_11252,c_30588])).

tff(c_30891,plain,(
    ! [B_813] :
      ( r1_tarski(u1_struct_0(B_813),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_813,k1_tsep_1('#skF_1','#skF_4','#skF_4'))
      | ~ m1_pre_topc(B_813,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40,c_30602])).

tff(c_28,plain,(
    ! [B_64,C_66,A_60] :
      ( m1_pre_topc(B_64,C_66)
      | ~ r1_tarski(u1_struct_0(B_64),u1_struct_0(C_66))
      | ~ m1_pre_topc(C_66,A_60)
      | ~ m1_pre_topc(B_64,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_32851,plain,(
    ! [B_845,A_846] :
      ( m1_pre_topc(B_845,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_846)
      | ~ m1_pre_topc(B_845,A_846)
      | ~ l1_pre_topc(A_846)
      | ~ v2_pre_topc(A_846)
      | ~ m1_pre_topc(B_845,k1_tsep_1('#skF_1','#skF_4','#skF_4'))
      | ~ m1_pre_topc(B_845,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30891,c_28])).

tff(c_32857,plain,(
    ! [B_845] :
      ( m1_pre_topc(B_845,'#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_845,k1_tsep_1('#skF_1','#skF_4','#skF_4'))
      | ~ m1_pre_topc(B_845,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_32851])).

tff(c_32915,plain,(
    ! [B_850] :
      ( m1_pre_topc(B_850,'#skF_4')
      | ~ m1_pre_topc(B_850,k1_tsep_1('#skF_1','#skF_4','#skF_4'))
      | ~ m1_pre_topc(B_850,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_32857])).

tff(c_37734,plain,(
    ! [B_962,C_963] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_962,C_963),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_962,C_963),'#skF_1')
      | r1_tsep_1(B_962,C_963)
      | ~ m1_pre_topc(C_963,'#skF_4')
      | ~ m1_pre_topc(B_962,'#skF_4')
      | ~ m1_pre_topc(C_963,'#skF_1')
      | v2_struct_0(C_963)
      | ~ m1_pre_topc(B_962,'#skF_1')
      | v2_struct_0(B_962) ) ),
    inference(resolution,[status(thm)],[c_23957,c_32915])).

tff(c_37757,plain,(
    ! [B_21,C_22] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_21,C_22),'#skF_4')
      | r1_tsep_1(B_21,C_22)
      | ~ m1_pre_topc(C_22,'#skF_4')
      | ~ m1_pre_topc(B_21,'#skF_4')
      | ~ m1_pre_topc(C_22,'#skF_1')
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,'#skF_1')
      | v2_struct_0(B_21)
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_37734])).

tff(c_37781,plain,(
    ! [B_21,C_22] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_21,C_22),'#skF_4')
      | r1_tsep_1(B_21,C_22)
      | ~ m1_pre_topc(C_22,'#skF_4')
      | ~ m1_pre_topc(B_21,'#skF_4')
      | ~ m1_pre_topc(C_22,'#skF_1')
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,'#skF_1')
      | v2_struct_0(B_21)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_37757])).

tff(c_38091,plain,(
    ! [B_969,C_970] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_969,C_970),'#skF_4')
      | r1_tsep_1(B_969,C_970)
      | ~ m1_pre_topc(C_970,'#skF_4')
      | ~ m1_pre_topc(B_969,'#skF_4')
      | ~ m1_pre_topc(C_970,'#skF_1')
      | v2_struct_0(C_970)
      | ~ m1_pre_topc(B_969,'#skF_1')
      | v2_struct_0(B_969) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_37781])).

tff(c_30,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_38108,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38091,c_30])).

tff(c_38149,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_36,c_34,c_38108])).

tff(c_38151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_32,c_38149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.46/8.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.49/8.58  
% 16.49/8.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.49/8.59  %$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > k2_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.49/8.59  
% 16.49/8.59  %Foreground sorts:
% 16.49/8.59  
% 16.49/8.59  
% 16.49/8.59  %Background operators:
% 16.49/8.59  
% 16.49/8.59  
% 16.49/8.59  %Foreground operators:
% 16.49/8.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 16.49/8.59  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 16.49/8.59  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 16.49/8.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.49/8.59  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 16.49/8.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.49/8.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.49/8.59  tff('#skF_2', type, '#skF_2': $i).
% 16.49/8.59  tff('#skF_3', type, '#skF_3': $i).
% 16.49/8.59  tff('#skF_1', type, '#skF_1': $i).
% 16.49/8.59  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 16.49/8.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.49/8.59  tff('#skF_4', type, '#skF_4': $i).
% 16.49/8.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.49/8.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 16.49/8.59  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 16.49/8.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.49/8.59  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 16.49/8.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.49/8.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.49/8.59  
% 16.49/8.60  tff(f_203, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, D)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tmap_1)).
% 16.49/8.60  tff(f_86, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 16.49/8.60  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 16.49/8.60  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k2_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tmap_1)).
% 16.49/8.60  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, E)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tmap_1)).
% 16.49/8.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.49/8.60  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 16.49/8.60  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 16.49/8.60  tff(f_169, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 16.49/8.60  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_32, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_46, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_14, plain, (![A_20, B_21, C_22]: (m1_pre_topc(k2_tsep_1(A_20, B_21, C_22), A_20) | ~m1_pre_topc(C_22, A_20) | v2_struct_0(C_22) | ~m1_pre_topc(B_21, A_20) | v2_struct_0(B_21) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.49/8.60  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.60  tff(c_352, plain, (![A_107, B_108]: (k1_tsep_1(A_107, B_108, B_108)=g1_pre_topc(u1_struct_0(B_108), u1_pre_topc(B_108)) | ~m1_pre_topc(B_108, A_107) | v2_struct_0(B_108) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.49/8.60  tff(c_360, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k1_tsep_1('#skF_1', '#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_352])).
% 16.49/8.60  tff(c_377, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k1_tsep_1('#skF_1', '#skF_4', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_360])).
% 16.49/8.60  tff(c_378, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k1_tsep_1('#skF_1', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_40, c_377])).
% 16.49/8.60  tff(c_403, plain, (![A_109, B_110]: (k2_tsep_1(A_109, B_110, B_110)=g1_pre_topc(u1_struct_0(B_110), u1_pre_topc(B_110)) | ~m1_pre_topc(B_110, A_109) | v2_struct_0(B_110) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.49/8.60  tff(c_411, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k2_tsep_1('#skF_1', '#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_403])).
% 16.49/8.60  tff(c_431, plain, (k2_tsep_1('#skF_1', '#skF_4', '#skF_4')=k1_tsep_1('#skF_1', '#skF_4', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_378, c_411])).
% 16.49/8.60  tff(c_432, plain, (k2_tsep_1('#skF_1', '#skF_4', '#skF_4')=k1_tsep_1('#skF_1', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_40, c_431])).
% 16.49/8.61  tff(c_23909, plain, (![B_660, E_662, C_658, A_659, D_661]: (m1_pre_topc(k2_tsep_1(A_659, B_660, C_658), k2_tsep_1(A_659, D_661, E_662)) | r1_tsep_1(B_660, C_658) | ~m1_pre_topc(C_658, E_662) | ~m1_pre_topc(B_660, D_661) | ~m1_pre_topc(E_662, A_659) | v2_struct_0(E_662) | ~m1_pre_topc(D_661, A_659) | v2_struct_0(D_661) | ~m1_pre_topc(C_658, A_659) | v2_struct_0(C_658) | ~m1_pre_topc(B_660, A_659) | v2_struct_0(B_660) | ~l1_pre_topc(A_659) | ~v2_pre_topc(A_659) | v2_struct_0(A_659))), inference(cnfTransformation, [status(thm)], [f_155])).
% 16.49/8.61  tff(c_23935, plain, (![B_660, C_658]: (m1_pre_topc(k2_tsep_1('#skF_1', B_660, C_658), k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | r1_tsep_1(B_660, C_658) | ~m1_pre_topc(C_658, '#skF_4') | ~m1_pre_topc(B_660, '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_658, '#skF_1') | v2_struct_0(C_658) | ~m1_pre_topc(B_660, '#skF_1') | v2_struct_0(B_660) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_23909])).
% 16.49/8.61  tff(c_23956, plain, (![B_660, C_658]: (m1_pre_topc(k2_tsep_1('#skF_1', B_660, C_658), k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | r1_tsep_1(B_660, C_658) | ~m1_pre_topc(C_658, '#skF_4') | ~m1_pre_topc(B_660, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_658, '#skF_1') | v2_struct_0(C_658) | ~m1_pre_topc(B_660, '#skF_1') | v2_struct_0(B_660) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_38, c_38, c_23935])).
% 16.49/8.61  tff(c_23957, plain, (![B_660, C_658]: (m1_pre_topc(k2_tsep_1('#skF_1', B_660, C_658), k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | r1_tsep_1(B_660, C_658) | ~m1_pre_topc(C_658, '#skF_4') | ~m1_pre_topc(B_660, '#skF_4') | ~m1_pre_topc(C_658, '#skF_1') | v2_struct_0(C_658) | ~m1_pre_topc(B_660, '#skF_1') | v2_struct_0(B_660))), inference(negUnitSimplification, [status(thm)], [c_54, c_40, c_23956])).
% 16.49/8.61  tff(c_18, plain, (![A_20, B_21, C_22]: (~v2_struct_0(k2_tsep_1(A_20, B_21, C_22)) | ~m1_pre_topc(C_22, A_20) | v2_struct_0(C_22) | ~m1_pre_topc(B_21, A_20) | v2_struct_0(B_21) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.49/8.61  tff(c_453, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_432, c_18])).
% 16.49/8.61  tff(c_460, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_38, c_453])).
% 16.49/8.61  tff(c_461, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_40, c_460])).
% 16.49/8.61  tff(c_16, plain, (![A_20, B_21, C_22]: (v1_pre_topc(k2_tsep_1(A_20, B_21, C_22)) | ~m1_pre_topc(C_22, A_20) | v2_struct_0(C_22) | ~m1_pre_topc(B_21, A_20) | v2_struct_0(B_21) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.49/8.61  tff(c_450, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_432, c_16])).
% 16.49/8.61  tff(c_457, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_38, c_450])).
% 16.49/8.61  tff(c_458, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_40, c_457])).
% 16.49/8.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.49/8.61  tff(c_57, plain, (![A_79, B_80]: (k2_xboole_0(A_79, B_80)=B_80 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.49/8.61  tff(c_61, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_57])).
% 16.49/8.61  tff(c_463, plain, (![A_111, B_112, C_113]: (m1_pre_topc(k2_tsep_1(A_111, B_112, C_113), A_111) | ~m1_pre_topc(C_113, A_111) | v2_struct_0(C_113) | ~m1_pre_topc(B_112, A_111) | v2_struct_0(B_112) | ~l1_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.49/8.61  tff(c_474, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_4'), '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_432, c_463])).
% 16.49/8.61  tff(c_480, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_4'), '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_38, c_474])).
% 16.49/8.61  tff(c_481, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_40, c_480])).
% 16.49/8.61  tff(c_11234, plain, (![A_374, B_375, C_376]: (u1_struct_0(k1_tsep_1(A_374, B_375, C_376))=k2_xboole_0(u1_struct_0(B_375), u1_struct_0(C_376)) | ~m1_pre_topc(k1_tsep_1(A_374, B_375, C_376), A_374) | ~v1_pre_topc(k1_tsep_1(A_374, B_375, C_376)) | v2_struct_0(k1_tsep_1(A_374, B_375, C_376)) | ~m1_pre_topc(C_376, A_374) | v2_struct_0(C_376) | ~m1_pre_topc(B_375, A_374) | v2_struct_0(B_375) | ~l1_pre_topc(A_374) | v2_struct_0(A_374))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.49/8.61  tff(c_11240, plain, (k2_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_481, c_11234])).
% 16.49/8.61  tff(c_11251, plain, (u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_4'))=u1_struct_0('#skF_4') | v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_458, c_61, c_11240])).
% 16.49/8.61  tff(c_11252, plain, (u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_4'))=u1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_40, c_461, c_11251])).
% 16.49/8.61  tff(c_26, plain, (![B_64, C_66, A_60]: (r1_tarski(u1_struct_0(B_64), u1_struct_0(C_66)) | ~m1_pre_topc(B_64, C_66) | ~m1_pre_topc(C_66, A_60) | ~m1_pre_topc(B_64, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_169])).
% 16.49/8.61  tff(c_30551, plain, (![B_801, A_802, B_803, C_804]: (r1_tarski(u1_struct_0(B_801), u1_struct_0(k2_tsep_1(A_802, B_803, C_804))) | ~m1_pre_topc(B_801, k2_tsep_1(A_802, B_803, C_804)) | ~m1_pre_topc(B_801, A_802) | ~v2_pre_topc(A_802) | ~m1_pre_topc(C_804, A_802) | v2_struct_0(C_804) | ~m1_pre_topc(B_803, A_802) | v2_struct_0(B_803) | ~l1_pre_topc(A_802) | v2_struct_0(A_802))), inference(resolution, [status(thm)], [c_463, c_26])).
% 16.49/8.61  tff(c_30588, plain, (![B_801]: (r1_tarski(u1_struct_0(B_801), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_4'))) | ~m1_pre_topc(B_801, k2_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc(B_801, '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_30551])).
% 16.49/8.61  tff(c_30602, plain, (![B_801]: (r1_tarski(u1_struct_0(B_801), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_801, k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc(B_801, '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_38, c_52, c_432, c_11252, c_30588])).
% 16.49/8.61  tff(c_30891, plain, (![B_813]: (r1_tarski(u1_struct_0(B_813), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_813, k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc(B_813, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_40, c_30602])).
% 16.49/8.61  tff(c_28, plain, (![B_64, C_66, A_60]: (m1_pre_topc(B_64, C_66) | ~r1_tarski(u1_struct_0(B_64), u1_struct_0(C_66)) | ~m1_pre_topc(C_66, A_60) | ~m1_pre_topc(B_64, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_169])).
% 16.49/8.61  tff(c_32851, plain, (![B_845, A_846]: (m1_pre_topc(B_845, '#skF_4') | ~m1_pre_topc('#skF_4', A_846) | ~m1_pre_topc(B_845, A_846) | ~l1_pre_topc(A_846) | ~v2_pre_topc(A_846) | ~m1_pre_topc(B_845, k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc(B_845, '#skF_1'))), inference(resolution, [status(thm)], [c_30891, c_28])).
% 16.49/8.61  tff(c_32857, plain, (![B_845]: (m1_pre_topc(B_845, '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(B_845, k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc(B_845, '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_32851])).
% 16.49/8.61  tff(c_32915, plain, (![B_850]: (m1_pre_topc(B_850, '#skF_4') | ~m1_pre_topc(B_850, k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc(B_850, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_32857])).
% 16.49/8.61  tff(c_37734, plain, (![B_962, C_963]: (m1_pre_topc(k2_tsep_1('#skF_1', B_962, C_963), '#skF_4') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_962, C_963), '#skF_1') | r1_tsep_1(B_962, C_963) | ~m1_pre_topc(C_963, '#skF_4') | ~m1_pre_topc(B_962, '#skF_4') | ~m1_pre_topc(C_963, '#skF_1') | v2_struct_0(C_963) | ~m1_pre_topc(B_962, '#skF_1') | v2_struct_0(B_962))), inference(resolution, [status(thm)], [c_23957, c_32915])).
% 16.49/8.61  tff(c_37757, plain, (![B_21, C_22]: (m1_pre_topc(k2_tsep_1('#skF_1', B_21, C_22), '#skF_4') | r1_tsep_1(B_21, C_22) | ~m1_pre_topc(C_22, '#skF_4') | ~m1_pre_topc(B_21, '#skF_4') | ~m1_pre_topc(C_22, '#skF_1') | v2_struct_0(C_22) | ~m1_pre_topc(B_21, '#skF_1') | v2_struct_0(B_21) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_37734])).
% 16.49/8.61  tff(c_37781, plain, (![B_21, C_22]: (m1_pre_topc(k2_tsep_1('#skF_1', B_21, C_22), '#skF_4') | r1_tsep_1(B_21, C_22) | ~m1_pre_topc(C_22, '#skF_4') | ~m1_pre_topc(B_21, '#skF_4') | ~m1_pre_topc(C_22, '#skF_1') | v2_struct_0(C_22) | ~m1_pre_topc(B_21, '#skF_1') | v2_struct_0(B_21) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_37757])).
% 16.49/8.61  tff(c_38091, plain, (![B_969, C_970]: (m1_pre_topc(k2_tsep_1('#skF_1', B_969, C_970), '#skF_4') | r1_tsep_1(B_969, C_970) | ~m1_pre_topc(C_970, '#skF_4') | ~m1_pre_topc(B_969, '#skF_4') | ~m1_pre_topc(C_970, '#skF_1') | v2_struct_0(C_970) | ~m1_pre_topc(B_969, '#skF_1') | v2_struct_0(B_969))), inference(negUnitSimplification, [status(thm)], [c_54, c_37781])).
% 16.49/8.61  tff(c_30, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 16.49/8.61  tff(c_38108, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38091, c_30])).
% 16.49/8.61  tff(c_38149, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_36, c_34, c_38108])).
% 16.49/8.61  tff(c_38151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_44, c_32, c_38149])).
% 16.49/8.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.49/8.61  
% 16.49/8.61  Inference rules
% 16.49/8.61  ----------------------
% 16.49/8.61  #Ref     : 10
% 16.49/8.61  #Sup     : 7691
% 16.49/8.61  #Fact    : 0
% 16.49/8.61  #Define  : 0
% 16.49/8.61  #Split   : 302
% 16.49/8.61  #Chain   : 0
% 16.49/8.61  #Close   : 0
% 16.49/8.61  
% 16.49/8.61  Ordering : KBO
% 16.49/8.61  
% 16.49/8.61  Simplification rules
% 16.49/8.61  ----------------------
% 16.49/8.61  #Subsume      : 1838
% 16.49/8.61  #Demod        : 22503
% 16.49/8.61  #Tautology    : 2021
% 16.49/8.61  #SimpNegUnit  : 3265
% 16.49/8.61  #BackRed      : 129
% 16.49/8.61  
% 16.49/8.61  #Partial instantiations: 0
% 16.49/8.61  #Strategies tried      : 1
% 16.49/8.61  
% 16.49/8.61  Timing (in seconds)
% 16.49/8.61  ----------------------
% 16.49/8.61  Preprocessing        : 0.33
% 16.49/8.61  Parsing              : 0.18
% 16.49/8.61  CNF conversion       : 0.03
% 16.49/8.61  Main loop            : 7.50
% 16.49/8.61  Inferencing          : 1.78
% 16.49/8.61  Reduction            : 3.45
% 16.49/8.61  Demodulation         : 2.73
% 16.49/8.61  BG Simplification    : 0.23
% 16.49/8.61  Subsumption          : 1.68
% 16.49/8.61  Abstraction          : 0.42
% 16.49/8.61  MUC search           : 0.00
% 16.49/8.61  Cooper               : 0.00
% 16.49/8.61  Total                : 7.87
% 16.49/8.61  Index Insertion      : 0.00
% 16.49/8.61  Index Deletion       : 0.00
% 16.49/8.61  Index Matching       : 0.00
% 16.49/8.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
