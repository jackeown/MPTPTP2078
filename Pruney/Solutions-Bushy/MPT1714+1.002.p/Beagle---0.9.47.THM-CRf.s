%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1714+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:17 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 242 expanded)
%              Number of leaves         :   23 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  209 ( 995 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_110,negated_conjecture,(
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
                   => ( m1_pre_topc(B,C)
                     => ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) )
                        | ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_66,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_290,plain,(
    ! [B_73,A_74] :
      ( l1_pre_topc(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_302,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_290])).

tff(c_312,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_302])).

tff(c_6,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_293,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_290])).

tff(c_305,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_293])).

tff(c_225,plain,(
    ! [B_66,A_67] :
      ( l1_pre_topc(B_66)
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_228,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_225])).

tff(c_240,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_228])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_231,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_225])).

tff(c_243,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_231])).

tff(c_22,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44,plain,(
    ! [B_32,A_33] :
      ( l1_pre_topc(B_32)
      | ~ m1_pre_topc(B_32,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_44])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_50])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_109,plain,(
    ! [B_46,C_47,A_48] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0(C_47))
      | ~ m1_pre_topc(B_46,C_47)
      | ~ m1_pre_topc(C_47,A_48)
      | ~ m1_pre_topc(B_46,A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_113,plain,(
    ! [B_46] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_46,'#skF_2')
      | ~ m1_pre_topc(B_46,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_109])).

tff(c_149,plain,(
    ! [B_54] :
      ( r1_tarski(u1_struct_0(B_54),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_54,'#skF_2')
      | ~ m1_pre_topc(B_54,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_113])).

tff(c_84,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(u1_struct_0(A_39),u1_struct_0(B_40))
      | ~ r1_tsep_1(A_39,B_40)
      | ~ l1_struct_0(B_40)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_17,C_19,B_18] :
      ( r1_xboole_0(A_17,C_19)
      | ~ r1_xboole_0(B_18,C_19)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_87,plain,(
    ! [A_17,B_40,A_39] :
      ( r1_xboole_0(A_17,u1_struct_0(B_40))
      | ~ r1_tarski(A_17,u1_struct_0(A_39))
      | ~ r1_tsep_1(A_39,B_40)
      | ~ l1_struct_0(B_40)
      | ~ l1_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_84,c_16])).

tff(c_155,plain,(
    ! [B_54,B_40] :
      ( r1_xboole_0(u1_struct_0(B_54),u1_struct_0(B_40))
      | ~ r1_tsep_1('#skF_2',B_40)
      | ~ l1_struct_0(B_40)
      | ~ l1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_54,'#skF_2')
      | ~ m1_pre_topc(B_54,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_149,c_87])).

tff(c_157,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_160,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_160])).

tff(c_166,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_47,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_59,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_47])).

tff(c_56,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_44])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_56])).

tff(c_18,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_70,plain,(
    ! [B_37,A_38] :
      ( r1_tsep_1(B_37,A_38)
      | ~ r1_tsep_1(A_38,B_37)
      | ~ l1_struct_0(B_37)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_73,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_74,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_77,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_77])).

tff(c_82,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_88,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_91,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_91])).

tff(c_97,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_83,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_117,plain,(
    ! [B_46] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_46,'#skF_3')
      | ~ m1_pre_topc(B_46,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_109])).

tff(c_136,plain,(
    ! [B_50] :
      ( r1_tarski(u1_struct_0(B_50),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_50,'#skF_3')
      | ~ m1_pre_topc(B_50,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_117])).

tff(c_138,plain,(
    ! [B_50,B_40] :
      ( r1_xboole_0(u1_struct_0(B_50),u1_struct_0(B_40))
      | ~ r1_tsep_1('#skF_3',B_40)
      | ~ l1_struct_0(B_40)
      | ~ l1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_50,'#skF_3')
      | ~ m1_pre_topc(B_50,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_136,c_87])).

tff(c_167,plain,(
    ! [B_55,B_56] :
      ( r1_xboole_0(u1_struct_0(B_55),u1_struct_0(B_56))
      | ~ r1_tsep_1('#skF_3',B_56)
      | ~ l1_struct_0(B_56)
      | ~ m1_pre_topc(B_55,'#skF_3')
      | ~ m1_pre_topc(B_55,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_138])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( r1_tsep_1(A_1,B_3)
      | ~ r1_xboole_0(u1_struct_0(A_1),u1_struct_0(B_3))
      | ~ l1_struct_0(B_3)
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_192,plain,(
    ! [B_63,B_64] :
      ( r1_tsep_1(B_63,B_64)
      | ~ l1_struct_0(B_63)
      | ~ r1_tsep_1('#skF_3',B_64)
      | ~ l1_struct_0(B_64)
      | ~ m1_pre_topc(B_63,'#skF_3')
      | ~ m1_pre_topc(B_63,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_194,plain,(
    ! [B_63] :
      ( r1_tsep_1(B_63,'#skF_4')
      | ~ l1_struct_0(B_63)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_63,'#skF_3')
      | ~ m1_pre_topc(B_63,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_192])).

tff(c_198,plain,(
    ! [B_65] :
      ( r1_tsep_1(B_65,'#skF_4')
      | ~ l1_struct_0(B_65)
      | ~ m1_pre_topc(B_65,'#skF_3')
      | ~ m1_pre_topc(B_65,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_194])).

tff(c_20,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_43,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_209,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_198,c_43])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22,c_166,c_209])).

tff(c_223,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_224,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_251,plain,(
    ! [B_71,A_72] :
      ( r1_tsep_1(B_71,A_72)
      | ~ r1_tsep_1(A_72,B_71)
      | ~ l1_struct_0(B_71)
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_253,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_224,c_251])).

tff(c_258,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_253])).

tff(c_260,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_263,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_260])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_263])).

tff(c_268,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_282,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_282])).

tff(c_288,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_287,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_316,plain,(
    ! [B_78,A_79] :
      ( r1_tsep_1(B_78,A_79)
      | ~ r1_tsep_1(A_79,B_78)
      | ~ l1_struct_0(B_78)
      | ~ l1_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_318,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_287,c_316])).

tff(c_321,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_318])).

tff(c_322,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_325,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_322])).

tff(c_329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_325])).

tff(c_330,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_334,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_330])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_334])).

%------------------------------------------------------------------------------
