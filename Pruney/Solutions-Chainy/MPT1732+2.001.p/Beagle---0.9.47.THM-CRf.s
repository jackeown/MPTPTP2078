%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:46 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 757 expanded)
%              Number of leaves         :   27 ( 237 expanded)
%              Depth                    :   15
%              Number of atoms          :  411 (3772 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_tsep_1 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_168,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(B,C)
                     => ( ( ~ r1_tsep_1(k2_tsep_1(A,B,C),D)
                         => ( ~ r1_tsep_1(B,D)
                            & ~ r1_tsep_1(C,D) ) )
                        & ( ~ r1_tsep_1(D,k2_tsep_1(A,B,C))
                         => ( ~ r1_tsep_1(D,B)
                            & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tmap_1)).

tff(f_73,axiom,(
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

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_107,axiom,(
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
             => ( ~ r1_tsep_1(B,C)
               => ( m1_pre_topc(k2_tsep_1(A,B,C),B)
                  & m1_pre_topc(k2_tsep_1(A,B,C),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_121,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1232,plain,(
    ! [A_232,B_233,C_234] :
      ( m1_pre_topc(k2_tsep_1(A_232,B_233,C_234),A_232)
      | ~ m1_pre_topc(C_234,A_232)
      | v2_struct_0(C_234)
      | ~ m1_pre_topc(B_233,A_232)
      | v2_struct_0(B_233)
      | ~ l1_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1270,plain,(
    ! [A_240,B_241,C_242] :
      ( l1_pre_topc(k2_tsep_1(A_240,B_241,C_242))
      | ~ m1_pre_topc(C_242,A_240)
      | v2_struct_0(C_242)
      | ~ m1_pre_topc(B_241,A_240)
      | v2_struct_0(B_241)
      | ~ l1_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(resolution,[status(thm)],[c_1232,c_6])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_56,plain,(
    ! [B_42,A_43] :
      ( l1_pre_topc(B_42)
      | ~ m1_pre_topc(B_42,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_56])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_65])).

tff(c_59,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_59])).

tff(c_28,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_620,plain,(
    ! [A_134,B_135,C_136] :
      ( m1_pre_topc(k2_tsep_1(A_134,B_135,C_136),B_135)
      | r1_tsep_1(B_135,C_136)
      | ~ m1_pre_topc(C_136,A_134)
      | v2_struct_0(C_136)
      | ~ m1_pre_topc(B_135,A_134)
      | v2_struct_0(B_135)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_325,plain,(
    ! [A_95,B_96,C_97] :
      ( m1_pre_topc(k2_tsep_1(A_95,B_96,C_97),A_95)
      | ~ m1_pre_topc(C_97,A_95)
      | v2_struct_0(C_97)
      | ~ m1_pre_topc(B_96,A_95)
      | v2_struct_0(B_96)
      | ~ l1_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_78,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( r1_tsep_1(B_15,A_14)
      | ~ r1_tsep_1(A_14,B_15)
      | ~ l1_struct_0(B_15)
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_81,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_18])).

tff(c_82,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_85,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_85])).

tff(c_91,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_90,plain,
    ( ~ l1_struct_0('#skF_2')
    | r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_92,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_99,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_92])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_99])).

tff(c_104,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_105,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_123,plain,(
    ! [B_61,C_62,A_63] :
      ( r1_tarski(u1_struct_0(B_61),u1_struct_0(C_62))
      | ~ m1_pre_topc(B_61,C_62)
      | ~ m1_pre_topc(C_62,A_63)
      | ~ m1_pre_topc(B_61,A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_125,plain,(
    ! [B_61] :
      ( r1_tarski(u1_struct_0(B_61),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_61,'#skF_2')
      | ~ m1_pre_topc(B_61,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_139,plain,(
    ! [B_64] :
      ( r1_tarski(u1_struct_0(B_64),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_64,'#skF_2')
      | ~ m1_pre_topc(B_64,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_125])).

tff(c_113,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(u1_struct_0(A_53),u1_struct_0(B_54))
      | ~ r1_tsep_1(A_53,B_54)
      | ~ l1_struct_0(B_54)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_1,B_54,A_53] :
      ( r1_xboole_0(A_1,u1_struct_0(B_54))
      | ~ r1_tarski(A_1,u1_struct_0(A_53))
      | ~ r1_tsep_1(A_53,B_54)
      | ~ l1_struct_0(B_54)
      | ~ l1_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_143,plain,(
    ! [B_64,B_54] :
      ( r1_xboole_0(u1_struct_0(B_64),u1_struct_0(B_54))
      | ~ r1_tsep_1('#skF_2',B_54)
      | ~ l1_struct_0(B_54)
      | ~ l1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_64,'#skF_2')
      | ~ m1_pre_topc(B_64,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_139,c_120])).

tff(c_174,plain,(
    ! [B_67,B_68] :
      ( r1_xboole_0(u1_struct_0(B_67),u1_struct_0(B_68))
      | ~ r1_tsep_1('#skF_2',B_68)
      | ~ l1_struct_0(B_68)
      | ~ m1_pre_topc(B_67,'#skF_2')
      | ~ m1_pre_topc(B_67,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_143])).

tff(c_8,plain,(
    ! [A_8,B_10] :
      ( r1_tsep_1(A_8,B_10)
      | ~ r1_xboole_0(u1_struct_0(A_8),u1_struct_0(B_10))
      | ~ l1_struct_0(B_10)
      | ~ l1_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_199,plain,(
    ! [B_76,B_77] :
      ( r1_tsep_1(B_76,B_77)
      | ~ l1_struct_0(B_76)
      | ~ r1_tsep_1('#skF_2',B_77)
      | ~ l1_struct_0(B_77)
      | ~ m1_pre_topc(B_76,'#skF_2')
      | ~ m1_pre_topc(B_76,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_174,c_8])).

tff(c_201,plain,(
    ! [B_76] :
      ( r1_tsep_1(B_76,'#skF_4')
      | ~ l1_struct_0(B_76)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_76,'#skF_2')
      | ~ m1_pre_topc(B_76,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_104,c_199])).

tff(c_205,plain,(
    ! [B_78] :
      ( r1_tsep_1(B_78,'#skF_4')
      | ~ l1_struct_0(B_78)
      | ~ m1_pre_topc(B_78,'#skF_2')
      | ~ m1_pre_topc(B_78,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_201])).

tff(c_50,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_77,plain,(
    ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_217,plain,
    ( ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_205,c_77])).

tff(c_227,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_328,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_325,c_227])).

tff(c_336,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_34,c_328])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_336])).

tff(c_340,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_345,plain,
    ( l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_340,c_6])).

tff(c_351,plain,(
    l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_345])).

tff(c_339,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_352,plain,(
    ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_355,plain,(
    ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_352])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_355])).

tff(c_360,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_623,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_620,c_360])).

tff(c_631,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_34,c_623])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_28,c_631])).

tff(c_635,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_56])).

tff(c_71,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_62])).

tff(c_953,plain,(
    ! [A_191,B_192,C_193] :
      ( m1_pre_topc(k2_tsep_1(A_191,B_192,C_193),C_193)
      | r1_tsep_1(B_192,C_193)
      | ~ m1_pre_topc(C_193,A_191)
      | v2_struct_0(C_193)
      | ~ m1_pre_topc(B_192,A_191)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_824,plain,(
    ! [A_171,B_172,C_173] :
      ( m1_pre_topc(k2_tsep_1(A_171,B_172,C_173),A_171)
      | ~ m1_pre_topc(C_173,A_171)
      | v2_struct_0(C_173)
      | ~ m1_pre_topc(B_172,A_171)
      | v2_struct_0(B_172)
      | ~ l1_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_634,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_636,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_634])).

tff(c_639,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_636,c_18])).

tff(c_640,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_639])).

tff(c_643,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_640])).

tff(c_647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_643])).

tff(c_648,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_650,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_648])).

tff(c_653,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_650])).

tff(c_657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_653])).

tff(c_659,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_648])).

tff(c_649,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_677,plain,(
    ! [B_147,C_148,A_149] :
      ( r1_tarski(u1_struct_0(B_147),u1_struct_0(C_148))
      | ~ m1_pre_topc(B_147,C_148)
      | ~ m1_pre_topc(C_148,A_149)
      | ~ m1_pre_topc(B_147,A_149)
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_681,plain,(
    ! [B_147] :
      ( r1_tarski(u1_struct_0(B_147),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_147,'#skF_3')
      | ~ m1_pre_topc(B_147,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_677])).

tff(c_709,plain,(
    ! [B_152] :
      ( r1_tarski(u1_struct_0(B_152),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_152,'#skF_3')
      | ~ m1_pre_topc(B_152,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_681])).

tff(c_666,plain,(
    ! [A_137,B_138] :
      ( r1_xboole_0(u1_struct_0(A_137),u1_struct_0(B_138))
      | ~ r1_tsep_1(A_137,B_138)
      | ~ l1_struct_0(B_138)
      | ~ l1_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_669,plain,(
    ! [A_1,B_138,A_137] :
      ( r1_xboole_0(A_1,u1_struct_0(B_138))
      | ~ r1_tarski(A_1,u1_struct_0(A_137))
      | ~ r1_tsep_1(A_137,B_138)
      | ~ l1_struct_0(B_138)
      | ~ l1_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_666,c_2])).

tff(c_713,plain,(
    ! [B_152,B_138] :
      ( r1_xboole_0(u1_struct_0(B_152),u1_struct_0(B_138))
      | ~ r1_tsep_1('#skF_3',B_138)
      | ~ l1_struct_0(B_138)
      | ~ l1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_152,'#skF_3')
      | ~ m1_pre_topc(B_152,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_709,c_669])).

tff(c_727,plain,(
    ! [B_158,B_159] :
      ( r1_xboole_0(u1_struct_0(B_158),u1_struct_0(B_159))
      | ~ r1_tsep_1('#skF_3',B_159)
      | ~ l1_struct_0(B_159)
      | ~ m1_pre_topc(B_158,'#skF_3')
      | ~ m1_pre_topc(B_158,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_713])).

tff(c_766,plain,(
    ! [B_164,B_165] :
      ( r1_tsep_1(B_164,B_165)
      | ~ l1_struct_0(B_164)
      | ~ r1_tsep_1('#skF_3',B_165)
      | ~ l1_struct_0(B_165)
      | ~ m1_pre_topc(B_164,'#skF_3')
      | ~ m1_pre_topc(B_164,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_727,c_8])).

tff(c_773,plain,(
    ! [B_164] :
      ( r1_tsep_1(B_164,'#skF_4')
      | ~ l1_struct_0(B_164)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_164,'#skF_3')
      | ~ m1_pre_topc(B_164,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_636,c_766])).

tff(c_781,plain,(
    ! [B_166] :
      ( r1_tsep_1(B_166,'#skF_4')
      | ~ l1_struct_0(B_166)
      | ~ m1_pre_topc(B_166,'#skF_3')
      | ~ m1_pre_topc(B_166,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_773])).

tff(c_799,plain,
    ( ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_781,c_77])).

tff(c_821,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_799])).

tff(c_827,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_824,c_821])).

tff(c_835,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_34,c_827])).

tff(c_837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_835])).

tff(c_839,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_799])).

tff(c_844,plain,
    ( l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_839,c_6])).

tff(c_850,plain,(
    l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_844])).

tff(c_838,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_799])).

tff(c_851,plain,(
    ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_838])).

tff(c_854,plain,(
    ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_851])).

tff(c_858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_854])).

tff(c_859,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_838])).

tff(c_956,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_953,c_859])).

tff(c_964,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_34,c_956])).

tff(c_966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_28,c_964])).

tff(c_968,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_967,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_969,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_971,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_969,c_18])).

tff(c_974,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_968,c_971])).

tff(c_975,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_974])).

tff(c_978,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_975])).

tff(c_982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_978])).

tff(c_983,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_974])).

tff(c_987,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_983])).

tff(c_991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_987])).

tff(c_992,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_995,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_992,c_18])).

tff(c_998,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_995])).

tff(c_999,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_998])).

tff(c_1002,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_999])).

tff(c_1006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1002])).

tff(c_1007,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_998])).

tff(c_1011,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1007])).

tff(c_1015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1011])).

tff(c_1017,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1058,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_54])).

tff(c_1016,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1018,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1016])).

tff(c_1021,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1018,c_18])).

tff(c_1025,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1021])).

tff(c_1032,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1025])).

tff(c_1036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1032])).

tff(c_1038,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1021])).

tff(c_1024,plain,
    ( r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1017,c_18])).

tff(c_1069,plain,
    ( r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_1024])).

tff(c_1070,plain,(
    ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1058,c_1069])).

tff(c_1074,plain,(
    ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_1070])).

tff(c_1273,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1270,c_1074])).

tff(c_1276,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_34,c_1273])).

tff(c_1278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_1276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:36:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.61  
% 3.61/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.61  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_tsep_1 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.61/1.61  
% 3.61/1.61  %Foreground sorts:
% 3.61/1.61  
% 3.61/1.61  
% 3.61/1.61  %Background operators:
% 3.61/1.61  
% 3.61/1.61  
% 3.61/1.61  %Foreground operators:
% 3.61/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.61/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.61/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.61/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.61  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.61/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.61/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.61/1.61  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 3.61/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.61/1.61  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.61/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.61/1.61  
% 3.96/1.64  tff(f_168, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => ((~r1_tsep_1(k2_tsep_1(A, B, C), D) => (~r1_tsep_1(B, D) & ~r1_tsep_1(C, D))) & (~r1_tsep_1(D, k2_tsep_1(A, B, C)) => (~r1_tsep_1(D, B) & ~r1_tsep_1(D, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tmap_1)).
% 3.96/1.64  tff(f_73, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 3.96/1.64  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.96/1.64  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.96/1.64  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (m1_pre_topc(k2_tsep_1(A, B, C), B) & m1_pre_topc(k2_tsep_1(A, B, C), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tsep_1)).
% 3.96/1.64  tff(f_81, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.96/1.64  tff(f_121, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.96/1.64  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.96/1.64  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.96/1.64  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_1232, plain, (![A_232, B_233, C_234]: (m1_pre_topc(k2_tsep_1(A_232, B_233, C_234), A_232) | ~m1_pre_topc(C_234, A_232) | v2_struct_0(C_234) | ~m1_pre_topc(B_233, A_232) | v2_struct_0(B_233) | ~l1_pre_topc(A_232) | v2_struct_0(A_232))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.96/1.64  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.96/1.64  tff(c_1270, plain, (![A_240, B_241, C_242]: (l1_pre_topc(k2_tsep_1(A_240, B_241, C_242)) | ~m1_pre_topc(C_242, A_240) | v2_struct_0(C_242) | ~m1_pre_topc(B_241, A_240) | v2_struct_0(B_241) | ~l1_pre_topc(A_240) | v2_struct_0(A_240))), inference(resolution, [status(thm)], [c_1232, c_6])).
% 3.96/1.64  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.96/1.64  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_56, plain, (![B_42, A_43]: (l1_pre_topc(B_42) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.96/1.64  tff(c_65, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_56])).
% 3.96/1.64  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_65])).
% 3.96/1.64  tff(c_59, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_56])).
% 3.96/1.64  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_59])).
% 3.96/1.64  tff(c_28, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_620, plain, (![A_134, B_135, C_136]: (m1_pre_topc(k2_tsep_1(A_134, B_135, C_136), B_135) | r1_tsep_1(B_135, C_136) | ~m1_pre_topc(C_136, A_134) | v2_struct_0(C_136) | ~m1_pre_topc(B_135, A_134) | v2_struct_0(B_135) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.96/1.64  tff(c_325, plain, (![A_95, B_96, C_97]: (m1_pre_topc(k2_tsep_1(A_95, B_96, C_97), A_95) | ~m1_pre_topc(C_97, A_95) | v2_struct_0(C_97) | ~m1_pre_topc(B_96, A_95) | v2_struct_0(B_96) | ~l1_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.96/1.64  tff(c_48, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_78, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 3.96/1.64  tff(c_18, plain, (![B_15, A_14]: (r1_tsep_1(B_15, A_14) | ~r1_tsep_1(A_14, B_15) | ~l1_struct_0(B_15) | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.96/1.64  tff(c_81, plain, (r1_tsep_1('#skF_2', '#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_18])).
% 3.96/1.64  tff(c_82, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_81])).
% 3.96/1.64  tff(c_85, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_82])).
% 3.96/1.64  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_85])).
% 3.96/1.64  tff(c_91, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_81])).
% 3.96/1.64  tff(c_90, plain, (~l1_struct_0('#skF_2') | r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_81])).
% 3.96/1.64  tff(c_92, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_90])).
% 3.96/1.64  tff(c_99, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_92])).
% 3.96/1.64  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_99])).
% 3.96/1.64  tff(c_104, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_90])).
% 3.96/1.64  tff(c_105, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_90])).
% 3.96/1.64  tff(c_123, plain, (![B_61, C_62, A_63]: (r1_tarski(u1_struct_0(B_61), u1_struct_0(C_62)) | ~m1_pre_topc(B_61, C_62) | ~m1_pre_topc(C_62, A_63) | ~m1_pre_topc(B_61, A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.96/1.64  tff(c_125, plain, (![B_61]: (r1_tarski(u1_struct_0(B_61), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_61, '#skF_2') | ~m1_pre_topc(B_61, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_123])).
% 3.96/1.64  tff(c_139, plain, (![B_64]: (r1_tarski(u1_struct_0(B_64), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_64, '#skF_2') | ~m1_pre_topc(B_64, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_125])).
% 3.96/1.64  tff(c_113, plain, (![A_53, B_54]: (r1_xboole_0(u1_struct_0(A_53), u1_struct_0(B_54)) | ~r1_tsep_1(A_53, B_54) | ~l1_struct_0(B_54) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.96/1.64  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.64  tff(c_120, plain, (![A_1, B_54, A_53]: (r1_xboole_0(A_1, u1_struct_0(B_54)) | ~r1_tarski(A_1, u1_struct_0(A_53)) | ~r1_tsep_1(A_53, B_54) | ~l1_struct_0(B_54) | ~l1_struct_0(A_53))), inference(resolution, [status(thm)], [c_113, c_2])).
% 3.96/1.64  tff(c_143, plain, (![B_64, B_54]: (r1_xboole_0(u1_struct_0(B_64), u1_struct_0(B_54)) | ~r1_tsep_1('#skF_2', B_54) | ~l1_struct_0(B_54) | ~l1_struct_0('#skF_2') | ~m1_pre_topc(B_64, '#skF_2') | ~m1_pre_topc(B_64, '#skF_1'))), inference(resolution, [status(thm)], [c_139, c_120])).
% 3.96/1.64  tff(c_174, plain, (![B_67, B_68]: (r1_xboole_0(u1_struct_0(B_67), u1_struct_0(B_68)) | ~r1_tsep_1('#skF_2', B_68) | ~l1_struct_0(B_68) | ~m1_pre_topc(B_67, '#skF_2') | ~m1_pre_topc(B_67, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_143])).
% 3.96/1.64  tff(c_8, plain, (![A_8, B_10]: (r1_tsep_1(A_8, B_10) | ~r1_xboole_0(u1_struct_0(A_8), u1_struct_0(B_10)) | ~l1_struct_0(B_10) | ~l1_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.96/1.64  tff(c_199, plain, (![B_76, B_77]: (r1_tsep_1(B_76, B_77) | ~l1_struct_0(B_76) | ~r1_tsep_1('#skF_2', B_77) | ~l1_struct_0(B_77) | ~m1_pre_topc(B_76, '#skF_2') | ~m1_pre_topc(B_76, '#skF_1'))), inference(resolution, [status(thm)], [c_174, c_8])).
% 3.96/1.64  tff(c_201, plain, (![B_76]: (r1_tsep_1(B_76, '#skF_4') | ~l1_struct_0(B_76) | ~l1_struct_0('#skF_4') | ~m1_pre_topc(B_76, '#skF_2') | ~m1_pre_topc(B_76, '#skF_1'))), inference(resolution, [status(thm)], [c_104, c_199])).
% 3.96/1.64  tff(c_205, plain, (![B_78]: (r1_tsep_1(B_78, '#skF_4') | ~l1_struct_0(B_78) | ~m1_pre_topc(B_78, '#skF_2') | ~m1_pre_topc(B_78, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_201])).
% 3.96/1.64  tff(c_50, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_77, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 3.96/1.64  tff(c_217, plain, (~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_205, c_77])).
% 3.96/1.64  tff(c_227, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_217])).
% 3.96/1.64  tff(c_328, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_325, c_227])).
% 3.96/1.64  tff(c_336, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_34, c_328])).
% 3.96/1.64  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_336])).
% 3.96/1.64  tff(c_340, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_217])).
% 3.96/1.64  tff(c_345, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_340, c_6])).
% 3.96/1.64  tff(c_351, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_345])).
% 3.96/1.64  tff(c_339, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_217])).
% 3.96/1.64  tff(c_352, plain, (~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_339])).
% 3.96/1.64  tff(c_355, plain, (~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_352])).
% 3.96/1.64  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_351, c_355])).
% 3.96/1.64  tff(c_360, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_339])).
% 3.96/1.64  tff(c_623, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_620, c_360])).
% 3.96/1.64  tff(c_631, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_34, c_623])).
% 3.96/1.64  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_28, c_631])).
% 3.96/1.64  tff(c_635, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 3.96/1.64  tff(c_62, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_56])).
% 3.96/1.64  tff(c_71, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_62])).
% 3.96/1.64  tff(c_953, plain, (![A_191, B_192, C_193]: (m1_pre_topc(k2_tsep_1(A_191, B_192, C_193), C_193) | r1_tsep_1(B_192, C_193) | ~m1_pre_topc(C_193, A_191) | v2_struct_0(C_193) | ~m1_pre_topc(B_192, A_191) | v2_struct_0(B_192) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.96/1.64  tff(c_824, plain, (![A_171, B_172, C_173]: (m1_pre_topc(k2_tsep_1(A_171, B_172, C_173), A_171) | ~m1_pre_topc(C_173, A_171) | v2_struct_0(C_173) | ~m1_pre_topc(B_172, A_171) | v2_struct_0(B_172) | ~l1_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.96/1.64  tff(c_634, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 3.96/1.64  tff(c_636, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_634])).
% 3.96/1.64  tff(c_639, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_636, c_18])).
% 3.96/1.64  tff(c_640, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_639])).
% 3.96/1.64  tff(c_643, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_640])).
% 3.96/1.64  tff(c_647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_643])).
% 3.96/1.64  tff(c_648, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_639])).
% 3.96/1.64  tff(c_650, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_648])).
% 3.96/1.64  tff(c_653, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_650])).
% 3.96/1.64  tff(c_657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_653])).
% 3.96/1.64  tff(c_659, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_648])).
% 3.96/1.64  tff(c_649, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_639])).
% 3.96/1.64  tff(c_677, plain, (![B_147, C_148, A_149]: (r1_tarski(u1_struct_0(B_147), u1_struct_0(C_148)) | ~m1_pre_topc(B_147, C_148) | ~m1_pre_topc(C_148, A_149) | ~m1_pre_topc(B_147, A_149) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.96/1.64  tff(c_681, plain, (![B_147]: (r1_tarski(u1_struct_0(B_147), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_147, '#skF_3') | ~m1_pre_topc(B_147, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_677])).
% 3.96/1.64  tff(c_709, plain, (![B_152]: (r1_tarski(u1_struct_0(B_152), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_152, '#skF_3') | ~m1_pre_topc(B_152, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_681])).
% 3.96/1.64  tff(c_666, plain, (![A_137, B_138]: (r1_xboole_0(u1_struct_0(A_137), u1_struct_0(B_138)) | ~r1_tsep_1(A_137, B_138) | ~l1_struct_0(B_138) | ~l1_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.96/1.64  tff(c_669, plain, (![A_1, B_138, A_137]: (r1_xboole_0(A_1, u1_struct_0(B_138)) | ~r1_tarski(A_1, u1_struct_0(A_137)) | ~r1_tsep_1(A_137, B_138) | ~l1_struct_0(B_138) | ~l1_struct_0(A_137))), inference(resolution, [status(thm)], [c_666, c_2])).
% 3.96/1.64  tff(c_713, plain, (![B_152, B_138]: (r1_xboole_0(u1_struct_0(B_152), u1_struct_0(B_138)) | ~r1_tsep_1('#skF_3', B_138) | ~l1_struct_0(B_138) | ~l1_struct_0('#skF_3') | ~m1_pre_topc(B_152, '#skF_3') | ~m1_pre_topc(B_152, '#skF_1'))), inference(resolution, [status(thm)], [c_709, c_669])).
% 3.96/1.64  tff(c_727, plain, (![B_158, B_159]: (r1_xboole_0(u1_struct_0(B_158), u1_struct_0(B_159)) | ~r1_tsep_1('#skF_3', B_159) | ~l1_struct_0(B_159) | ~m1_pre_topc(B_158, '#skF_3') | ~m1_pre_topc(B_158, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_649, c_713])).
% 3.96/1.64  tff(c_766, plain, (![B_164, B_165]: (r1_tsep_1(B_164, B_165) | ~l1_struct_0(B_164) | ~r1_tsep_1('#skF_3', B_165) | ~l1_struct_0(B_165) | ~m1_pre_topc(B_164, '#skF_3') | ~m1_pre_topc(B_164, '#skF_1'))), inference(resolution, [status(thm)], [c_727, c_8])).
% 3.96/1.64  tff(c_773, plain, (![B_164]: (r1_tsep_1(B_164, '#skF_4') | ~l1_struct_0(B_164) | ~l1_struct_0('#skF_4') | ~m1_pre_topc(B_164, '#skF_3') | ~m1_pre_topc(B_164, '#skF_1'))), inference(resolution, [status(thm)], [c_636, c_766])).
% 3.96/1.64  tff(c_781, plain, (![B_166]: (r1_tsep_1(B_166, '#skF_4') | ~l1_struct_0(B_166) | ~m1_pre_topc(B_166, '#skF_3') | ~m1_pre_topc(B_166, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_773])).
% 3.96/1.64  tff(c_799, plain, (~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_781, c_77])).
% 3.96/1.64  tff(c_821, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_799])).
% 3.96/1.64  tff(c_827, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_824, c_821])).
% 3.96/1.64  tff(c_835, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_34, c_827])).
% 3.96/1.64  tff(c_837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_835])).
% 3.96/1.64  tff(c_839, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_799])).
% 3.96/1.64  tff(c_844, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_839, c_6])).
% 3.96/1.64  tff(c_850, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_844])).
% 3.96/1.64  tff(c_838, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_799])).
% 3.96/1.64  tff(c_851, plain, (~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_838])).
% 3.96/1.64  tff(c_854, plain, (~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_851])).
% 3.96/1.64  tff(c_858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_850, c_854])).
% 3.96/1.64  tff(c_859, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_838])).
% 3.96/1.64  tff(c_956, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_953, c_859])).
% 3.96/1.64  tff(c_964, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_34, c_956])).
% 3.96/1.64  tff(c_966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_28, c_964])).
% 3.96/1.64  tff(c_968, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_634])).
% 3.96/1.64  tff(c_967, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_634])).
% 3.96/1.64  tff(c_969, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_967])).
% 3.96/1.64  tff(c_971, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_969, c_18])).
% 3.96/1.64  tff(c_974, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_968, c_971])).
% 3.96/1.64  tff(c_975, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_974])).
% 3.96/1.64  tff(c_978, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_975])).
% 3.96/1.64  tff(c_982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_978])).
% 3.96/1.64  tff(c_983, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_974])).
% 3.96/1.64  tff(c_987, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_983])).
% 3.96/1.64  tff(c_991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_987])).
% 3.96/1.64  tff(c_992, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_967])).
% 3.96/1.64  tff(c_995, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_992, c_18])).
% 3.96/1.64  tff(c_998, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_635, c_995])).
% 3.96/1.64  tff(c_999, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_998])).
% 3.96/1.64  tff(c_1002, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_999])).
% 3.96/1.64  tff(c_1006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1002])).
% 3.96/1.64  tff(c_1007, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_998])).
% 3.96/1.64  tff(c_1011, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1007])).
% 3.96/1.64  tff(c_1015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1011])).
% 3.96/1.64  tff(c_1017, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 3.96/1.64  tff(c_54, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.96/1.64  tff(c_1058, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_54])).
% 3.96/1.64  tff(c_1016, plain, (r1_tsep_1('#skF_4', '#skF_2') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.96/1.64  tff(c_1018, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1016])).
% 3.96/1.64  tff(c_1021, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1018, c_18])).
% 3.96/1.64  tff(c_1025, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1021])).
% 3.96/1.64  tff(c_1032, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1025])).
% 3.96/1.64  tff(c_1036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1032])).
% 3.96/1.64  tff(c_1038, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1021])).
% 3.96/1.64  tff(c_1024, plain, (r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4') | ~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1017, c_18])).
% 3.96/1.64  tff(c_1069, plain, (r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_1024])).
% 3.96/1.64  tff(c_1070, plain, (~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1058, c_1069])).
% 3.96/1.64  tff(c_1074, plain, (~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_1070])).
% 3.96/1.64  tff(c_1273, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1270, c_1074])).
% 3.96/1.64  tff(c_1276, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_34, c_1273])).
% 3.96/1.64  tff(c_1278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_1276])).
% 3.96/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.64  
% 3.96/1.64  Inference rules
% 3.96/1.64  ----------------------
% 3.96/1.64  #Ref     : 0
% 3.96/1.64  #Sup     : 217
% 3.96/1.64  #Fact    : 0
% 3.96/1.64  #Define  : 0
% 3.96/1.64  #Split   : 39
% 3.96/1.64  #Chain   : 0
% 3.96/1.64  #Close   : 0
% 3.96/1.64  
% 3.96/1.64  Ordering : KBO
% 3.96/1.64  
% 3.96/1.64  Simplification rules
% 3.96/1.64  ----------------------
% 3.96/1.64  #Subsume      : 58
% 3.96/1.64  #Demod        : 240
% 3.96/1.64  #Tautology    : 21
% 3.96/1.64  #SimpNegUnit  : 8
% 3.96/1.64  #BackRed      : 0
% 3.96/1.64  
% 3.96/1.64  #Partial instantiations: 0
% 3.96/1.64  #Strategies tried      : 1
% 3.96/1.64  
% 3.96/1.64  Timing (in seconds)
% 3.96/1.64  ----------------------
% 3.96/1.64  Preprocessing        : 0.31
% 3.96/1.64  Parsing              : 0.18
% 3.96/1.64  CNF conversion       : 0.03
% 3.96/1.64  Main loop            : 0.54
% 3.96/1.64  Inferencing          : 0.20
% 3.96/1.64  Reduction            : 0.15
% 3.96/1.64  Demodulation         : 0.10
% 3.96/1.64  BG Simplification    : 0.02
% 3.96/1.64  Subsumption          : 0.13
% 3.96/1.64  Abstraction          : 0.02
% 3.96/1.64  MUC search           : 0.00
% 3.96/1.64  Cooper               : 0.00
% 3.96/1.64  Total                : 0.91
% 3.96/1.64  Index Insertion      : 0.00
% 3.96/1.64  Index Deletion       : 0.00
% 3.96/1.64  Index Matching       : 0.00
% 3.96/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
