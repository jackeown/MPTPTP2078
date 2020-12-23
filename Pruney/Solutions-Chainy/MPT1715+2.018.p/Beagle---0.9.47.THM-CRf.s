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
% DateTime   : Thu Dec  3 10:26:39 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
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

tff(f_111,negated_conjecture,(
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
                     => ( ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) )
                        | ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

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

tff(f_73,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_277,plain,(
    ! [B_73,A_74] :
      ( l1_pre_topc(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_280,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_277])).

tff(c_292,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_280])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_283,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_277])).

tff(c_295,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_283])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_225,plain,(
    ! [B_66,A_67] :
      ( l1_pre_topc(B_66)
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_237,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_225])).

tff(c_247,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_237])).

tff(c_228,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_225])).

tff(c_240,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_228])).

tff(c_22,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    ! [B_32,A_33] :
      ( l1_pre_topc(B_32)
      | ~ m1_pre_topc(B_32,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_44])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_50])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_109,plain,(
    ! [B_46,C_47,A_48] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0(C_47))
      | ~ m1_pre_topc(B_46,C_47)
      | ~ m1_pre_topc(C_47,A_48)
      | ~ m1_pre_topc(B_46,A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

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
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_1,B_40,A_39] :
      ( r1_xboole_0(A_1,u1_struct_0(B_40))
      | ~ r1_tarski(A_1,u1_struct_0(A_39))
      | ~ r1_tsep_1(A_39,B_40)
      | ~ l1_struct_0(B_40)
      | ~ l1_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

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
    inference(resolution,[status(thm)],[c_4,c_157])).

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

tff(c_20,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_43,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_70,plain,(
    ! [B_37,A_38] :
      ( r1_tsep_1(B_37,A_38)
      | ~ r1_tsep_1(A_38,B_37)
      | ~ l1_struct_0(B_37)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_73,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_43,c_70])).

tff(c_74,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_77,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_74])).

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
    inference(resolution,[status(thm)],[c_4,c_88])).

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

tff(c_8,plain,(
    ! [A_8,B_10] :
      ( r1_tsep_1(A_8,B_10)
      | ~ r1_xboole_0(u1_struct_0(A_8),u1_struct_0(B_10))
      | ~ l1_struct_0(B_10)
      | ~ l1_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_192,plain,(
    ! [B_63,B_64] :
      ( r1_tsep_1(B_63,B_64)
      | ~ l1_struct_0(B_63)
      | ~ r1_tsep_1('#skF_3',B_64)
      | ~ l1_struct_0(B_64)
      | ~ m1_pre_topc(B_63,'#skF_3')
      | ~ m1_pre_topc(B_63,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_167,c_8])).

tff(c_194,plain,(
    ! [B_63] :
      ( r1_tsep_1(B_63,'#skF_4')
      | ~ l1_struct_0(B_63)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_63,'#skF_3')
      | ~ m1_pre_topc(B_63,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_43,c_192])).

tff(c_198,plain,(
    ! [B_65] :
      ( r1_tsep_1(B_65,'#skF_4')
      | ~ l1_struct_0(B_65)
      | ~ m1_pre_topc(B_65,'#skF_3')
      | ~ m1_pre_topc(B_65,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_194])).

tff(c_18,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_209,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_198,c_42])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22,c_166,c_209])).

tff(c_224,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_223,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_251,plain,(
    ! [B_71,A_72] :
      ( r1_tsep_1(B_71,A_72)
      | ~ r1_tsep_1(A_72,B_71)
      | ~ l1_struct_0(B_71)
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_253,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_223,c_251])).

tff(c_256,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_253])).

tff(c_257,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_260,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_257])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_260])).

tff(c_265,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_269,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_265])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_269])).

tff(c_274,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_275,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_303,plain,(
    ! [B_78,A_79] :
      ( r1_tsep_1(B_78,A_79)
      | ~ r1_tsep_1(A_79,B_78)
      | ~ l1_struct_0(B_78)
      | ~ l1_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_307,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_275,c_303])).

tff(c_311,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_307])).

tff(c_312,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_315,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_312])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_315])).

tff(c_320,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_324,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_320])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:02:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.26  
% 2.23/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.27  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.23/1.27  
% 2.23/1.27  %Foreground sorts:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Background operators:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Foreground operators:
% 2.23/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.23/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.23/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.23/1.27  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.23/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.27  
% 2.23/1.29  tff(f_111, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 2.23/1.29  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.23/1.29  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.23/1.29  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.23/1.29  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.23/1.29  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.23/1.29  tff(f_59, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.23/1.29  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.23/1.29  tff(c_24, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.23/1.29  tff(c_277, plain, (![B_73, A_74]: (l1_pre_topc(B_73) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.29  tff(c_280, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_277])).
% 2.23/1.29  tff(c_292, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_280])).
% 2.23/1.29  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.29  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.23/1.29  tff(c_283, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_277])).
% 2.23/1.29  tff(c_295, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_283])).
% 2.23/1.29  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.23/1.29  tff(c_225, plain, (![B_66, A_67]: (l1_pre_topc(B_66) | ~m1_pre_topc(B_66, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.29  tff(c_237, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_225])).
% 2.23/1.29  tff(c_247, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_237])).
% 2.23/1.29  tff(c_228, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_225])).
% 2.23/1.29  tff(c_240, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_228])).
% 2.23/1.29  tff(c_22, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.23/1.29  tff(c_44, plain, (![B_32, A_33]: (l1_pre_topc(B_32) | ~m1_pre_topc(B_32, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.29  tff(c_50, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_44])).
% 2.23/1.29  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_50])).
% 2.23/1.29  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.23/1.29  tff(c_109, plain, (![B_46, C_47, A_48]: (r1_tarski(u1_struct_0(B_46), u1_struct_0(C_47)) | ~m1_pre_topc(B_46, C_47) | ~m1_pre_topc(C_47, A_48) | ~m1_pre_topc(B_46, A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.29  tff(c_113, plain, (![B_46]: (r1_tarski(u1_struct_0(B_46), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_46, '#skF_2') | ~m1_pre_topc(B_46, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_109])).
% 2.23/1.29  tff(c_149, plain, (![B_54]: (r1_tarski(u1_struct_0(B_54), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_54, '#skF_2') | ~m1_pre_topc(B_54, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_113])).
% 2.23/1.29  tff(c_84, plain, (![A_39, B_40]: (r1_xboole_0(u1_struct_0(A_39), u1_struct_0(B_40)) | ~r1_tsep_1(A_39, B_40) | ~l1_struct_0(B_40) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.29  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.29  tff(c_87, plain, (![A_1, B_40, A_39]: (r1_xboole_0(A_1, u1_struct_0(B_40)) | ~r1_tarski(A_1, u1_struct_0(A_39)) | ~r1_tsep_1(A_39, B_40) | ~l1_struct_0(B_40) | ~l1_struct_0(A_39))), inference(resolution, [status(thm)], [c_84, c_2])).
% 2.23/1.29  tff(c_155, plain, (![B_54, B_40]: (r1_xboole_0(u1_struct_0(B_54), u1_struct_0(B_40)) | ~r1_tsep_1('#skF_2', B_40) | ~l1_struct_0(B_40) | ~l1_struct_0('#skF_2') | ~m1_pre_topc(B_54, '#skF_2') | ~m1_pre_topc(B_54, '#skF_1'))), inference(resolution, [status(thm)], [c_149, c_87])).
% 2.23/1.29  tff(c_157, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_155])).
% 2.23/1.29  tff(c_160, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_157])).
% 2.23/1.29  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_160])).
% 2.23/1.29  tff(c_166, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_155])).
% 2.23/1.29  tff(c_47, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_44])).
% 2.23/1.29  tff(c_59, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_47])).
% 2.23/1.29  tff(c_56, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_44])).
% 2.23/1.29  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_56])).
% 2.23/1.29  tff(c_20, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.23/1.29  tff(c_43, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_20])).
% 2.23/1.29  tff(c_70, plain, (![B_37, A_38]: (r1_tsep_1(B_37, A_38) | ~r1_tsep_1(A_38, B_37) | ~l1_struct_0(B_37) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.29  tff(c_73, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_43, c_70])).
% 2.23/1.29  tff(c_74, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_73])).
% 2.23/1.29  tff(c_77, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_74])).
% 2.23/1.29  tff(c_81, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_77])).
% 2.23/1.29  tff(c_82, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_73])).
% 2.23/1.29  tff(c_88, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 2.23/1.29  tff(c_91, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_88])).
% 2.23/1.29  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_91])).
% 2.23/1.29  tff(c_97, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_82])).
% 2.23/1.29  tff(c_83, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_73])).
% 2.23/1.29  tff(c_117, plain, (![B_46]: (r1_tarski(u1_struct_0(B_46), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_46, '#skF_3') | ~m1_pre_topc(B_46, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_109])).
% 2.23/1.29  tff(c_136, plain, (![B_50]: (r1_tarski(u1_struct_0(B_50), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_50, '#skF_3') | ~m1_pre_topc(B_50, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_117])).
% 2.23/1.29  tff(c_138, plain, (![B_50, B_40]: (r1_xboole_0(u1_struct_0(B_50), u1_struct_0(B_40)) | ~r1_tsep_1('#skF_3', B_40) | ~l1_struct_0(B_40) | ~l1_struct_0('#skF_3') | ~m1_pre_topc(B_50, '#skF_3') | ~m1_pre_topc(B_50, '#skF_1'))), inference(resolution, [status(thm)], [c_136, c_87])).
% 2.23/1.29  tff(c_167, plain, (![B_55, B_56]: (r1_xboole_0(u1_struct_0(B_55), u1_struct_0(B_56)) | ~r1_tsep_1('#skF_3', B_56) | ~l1_struct_0(B_56) | ~m1_pre_topc(B_55, '#skF_3') | ~m1_pre_topc(B_55, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_138])).
% 2.23/1.29  tff(c_8, plain, (![A_8, B_10]: (r1_tsep_1(A_8, B_10) | ~r1_xboole_0(u1_struct_0(A_8), u1_struct_0(B_10)) | ~l1_struct_0(B_10) | ~l1_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.29  tff(c_192, plain, (![B_63, B_64]: (r1_tsep_1(B_63, B_64) | ~l1_struct_0(B_63) | ~r1_tsep_1('#skF_3', B_64) | ~l1_struct_0(B_64) | ~m1_pre_topc(B_63, '#skF_3') | ~m1_pre_topc(B_63, '#skF_1'))), inference(resolution, [status(thm)], [c_167, c_8])).
% 2.23/1.29  tff(c_194, plain, (![B_63]: (r1_tsep_1(B_63, '#skF_4') | ~l1_struct_0(B_63) | ~l1_struct_0('#skF_4') | ~m1_pre_topc(B_63, '#skF_3') | ~m1_pre_topc(B_63, '#skF_1'))), inference(resolution, [status(thm)], [c_43, c_192])).
% 2.23/1.29  tff(c_198, plain, (![B_65]: (r1_tsep_1(B_65, '#skF_4') | ~l1_struct_0(B_65) | ~m1_pre_topc(B_65, '#skF_3') | ~m1_pre_topc(B_65, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_194])).
% 2.23/1.29  tff(c_18, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.23/1.29  tff(c_42, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_18])).
% 2.23/1.29  tff(c_209, plain, (~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_198, c_42])).
% 2.23/1.29  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_22, c_166, c_209])).
% 2.23/1.29  tff(c_224, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 2.23/1.29  tff(c_223, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.23/1.29  tff(c_251, plain, (![B_71, A_72]: (r1_tsep_1(B_71, A_72) | ~r1_tsep_1(A_72, B_71) | ~l1_struct_0(B_71) | ~l1_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.29  tff(c_253, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_223, c_251])).
% 2.23/1.29  tff(c_256, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_224, c_253])).
% 2.23/1.29  tff(c_257, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_256])).
% 2.23/1.29  tff(c_260, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_257])).
% 2.23/1.29  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_260])).
% 2.23/1.29  tff(c_265, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_256])).
% 2.23/1.29  tff(c_269, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_265])).
% 2.23/1.29  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247, c_269])).
% 2.23/1.29  tff(c_274, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 2.23/1.29  tff(c_275, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_18])).
% 2.23/1.29  tff(c_303, plain, (![B_78, A_79]: (r1_tsep_1(B_78, A_79) | ~r1_tsep_1(A_79, B_78) | ~l1_struct_0(B_78) | ~l1_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.29  tff(c_307, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_275, c_303])).
% 2.23/1.29  tff(c_311, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_274, c_307])).
% 2.23/1.29  tff(c_312, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_311])).
% 2.23/1.29  tff(c_315, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_312])).
% 2.23/1.29  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_295, c_315])).
% 2.23/1.29  tff(c_320, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_311])).
% 2.23/1.29  tff(c_324, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_320])).
% 2.23/1.29  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_292, c_324])).
% 2.23/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  Inference rules
% 2.23/1.29  ----------------------
% 2.23/1.29  #Ref     : 0
% 2.23/1.29  #Sup     : 47
% 2.23/1.29  #Fact    : 0
% 2.23/1.29  #Define  : 0
% 2.23/1.29  #Split   : 9
% 2.23/1.29  #Chain   : 0
% 2.23/1.29  #Close   : 0
% 2.23/1.29  
% 2.23/1.29  Ordering : KBO
% 2.23/1.29  
% 2.23/1.29  Simplification rules
% 2.23/1.29  ----------------------
% 2.23/1.29  #Subsume      : 1
% 2.23/1.29  #Demod        : 46
% 2.23/1.29  #Tautology    : 8
% 2.23/1.29  #SimpNegUnit  : 2
% 2.23/1.29  #BackRed      : 0
% 2.23/1.29  
% 2.23/1.29  #Partial instantiations: 0
% 2.23/1.29  #Strategies tried      : 1
% 2.23/1.29  
% 2.23/1.29  Timing (in seconds)
% 2.23/1.29  ----------------------
% 2.23/1.29  Preprocessing        : 0.28
% 2.23/1.29  Parsing              : 0.16
% 2.23/1.29  CNF conversion       : 0.02
% 2.23/1.29  Main loop            : 0.23
% 2.23/1.29  Inferencing          : 0.09
% 2.23/1.29  Reduction            : 0.06
% 2.23/1.29  Demodulation         : 0.04
% 2.23/1.29  BG Simplification    : 0.02
% 2.23/1.29  Subsumption          : 0.04
% 2.23/1.29  Abstraction          : 0.01
% 2.23/1.29  MUC search           : 0.00
% 2.23/1.29  Cooper               : 0.00
% 2.23/1.29  Total                : 0.55
% 2.23/1.29  Index Insertion      : 0.00
% 2.23/1.29  Index Deletion       : 0.00
% 2.23/1.29  Index Matching       : 0.00
% 2.23/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
