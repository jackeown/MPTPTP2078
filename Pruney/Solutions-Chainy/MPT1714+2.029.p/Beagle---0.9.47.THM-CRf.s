%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:36 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 219 expanded)
%              Number of leaves         :   26 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  178 ( 809 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
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

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_267,plain,(
    ! [B_78,A_79] :
      ( l1_pre_topc(B_78)
      | ~ m1_pre_topc(B_78,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_276,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_267])).

tff(c_286,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_276])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_270,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_267])).

tff(c_282,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_270])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_198,plain,(
    ! [B_61,A_62] :
      ( l1_pre_topc(B_61)
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_210,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_198])).

tff(c_220,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_210])).

tff(c_207,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_198])).

tff(c_217,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_207])).

tff(c_52,plain,(
    ! [B_34,A_35] :
      ( l1_pre_topc(B_34)
      | ~ m1_pre_topc(B_34,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_55,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_67,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_55])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_61,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_52])).

tff(c_71,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_61])).

tff(c_64,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_74,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64])).

tff(c_20,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_45,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_77,plain,(
    ! [B_39,A_40] :
      ( r1_tsep_1(B_39,A_40)
      | ~ r1_tsep_1(A_40,B_39)
      | ~ l1_struct_0(B_39)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_45,c_77])).

tff(c_81,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_89,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_89])).

tff(c_94,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_99,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_99])).

tff(c_105,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_95,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_111,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(u1_struct_0(B_43),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(u1_struct_0(B_43),u1_struct_0(A_44))
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_118,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(u1_struct_0(A_49),u1_struct_0(B_50))
      | ~ r1_tsep_1(A_49,B_50)
      | ~ l1_struct_0(B_50)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_51,B_52,A_53] :
      ( r1_xboole_0(A_51,u1_struct_0(B_52))
      | ~ r1_tarski(A_51,u1_struct_0(A_53))
      | ~ r1_tsep_1(A_53,B_52)
      | ~ l1_struct_0(B_52)
      | ~ l1_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_130,plain,(
    ! [B_54,B_55,A_56] :
      ( r1_xboole_0(u1_struct_0(B_54),u1_struct_0(B_55))
      | ~ r1_tsep_1(A_56,B_55)
      | ~ l1_struct_0(B_55)
      | ~ l1_struct_0(A_56)
      | ~ m1_pre_topc(B_54,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_115,c_126])).

tff(c_134,plain,(
    ! [B_54] :
      ( r1_xboole_0(u1_struct_0(B_54),u1_struct_0('#skF_4'))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_54,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_45,c_130])).

tff(c_151,plain,(
    ! [B_58] :
      ( r1_xboole_0(u1_struct_0(B_58),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_58,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_95,c_105,c_134])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( r1_tsep_1(A_10,B_12)
      | ~ r1_xboole_0(u1_struct_0(A_10),u1_struct_0(B_12))
      | ~ l1_struct_0(B_12)
      | ~ l1_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    ! [B_58] :
      ( r1_tsep_1(B_58,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0(B_58)
      | ~ m1_pre_topc(B_58,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_151,c_12])).

tff(c_172,plain,(
    ! [B_60] :
      ( r1_tsep_1(B_60,'#skF_4')
      | ~ l1_struct_0(B_60)
      | ~ m1_pre_topc(B_60,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_154])).

tff(c_22,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_179,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_44])).

tff(c_188,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_179])).

tff(c_191,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_191])).

tff(c_197,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_196,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_230,plain,(
    ! [B_70,A_71] :
      ( r1_tsep_1(B_70,A_71)
      | ~ r1_tsep_1(A_71,B_70)
      | ~ l1_struct_0(B_70)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_232,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_230])).

tff(c_235,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_232])).

tff(c_236,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_244,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_236])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_244])).

tff(c_249,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_253,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_249])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_253])).

tff(c_258,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_259,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_293,plain,(
    ! [B_83,A_84] :
      ( r1_tsep_1(B_83,A_84)
      | ~ r1_tsep_1(A_84,B_83)
      | ~ l1_struct_0(B_83)
      | ~ l1_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_297,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_259,c_293])).

tff(c_301,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_297])).

tff(c_302,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_305,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_302])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_305])).

tff(c_310,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_314,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_310])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:17:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.26  
% 2.31/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.27  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.31/1.27  
% 2.31/1.27  %Foreground sorts:
% 2.31/1.27  
% 2.31/1.27  
% 2.31/1.27  %Background operators:
% 2.31/1.27  
% 2.31/1.27  
% 2.31/1.27  %Foreground operators:
% 2.31/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.31/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.31/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.31/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.31/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.31/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.31/1.27  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.31/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.31/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.27  
% 2.31/1.29  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 2.31/1.29  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.31/1.29  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.31/1.29  tff(f_63, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.31/1.29  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.31/1.29  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.31/1.29  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.31/1.29  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.31/1.29  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.31/1.29  tff(c_26, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.31/1.29  tff(c_267, plain, (![B_78, A_79]: (l1_pre_topc(B_78) | ~m1_pre_topc(B_78, A_79) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.31/1.29  tff(c_276, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_267])).
% 2.31/1.29  tff(c_286, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_276])).
% 2.31/1.29  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.29  tff(c_34, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.31/1.29  tff(c_270, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_267])).
% 2.31/1.29  tff(c_282, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_270])).
% 2.31/1.29  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.31/1.29  tff(c_198, plain, (![B_61, A_62]: (l1_pre_topc(B_61) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.31/1.29  tff(c_210, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_198])).
% 2.31/1.29  tff(c_220, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_210])).
% 2.31/1.29  tff(c_207, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_198])).
% 2.31/1.29  tff(c_217, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_207])).
% 2.31/1.29  tff(c_52, plain, (![B_34, A_35]: (l1_pre_topc(B_34) | ~m1_pre_topc(B_34, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.31/1.29  tff(c_55, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_52])).
% 2.31/1.29  tff(c_67, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_55])).
% 2.31/1.29  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.31/1.29  tff(c_61, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_52])).
% 2.31/1.29  tff(c_71, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_61])).
% 2.31/1.29  tff(c_64, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_52])).
% 2.31/1.29  tff(c_74, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_64])).
% 2.31/1.29  tff(c_20, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.31/1.29  tff(c_45, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_20])).
% 2.31/1.29  tff(c_77, plain, (![B_39, A_40]: (r1_tsep_1(B_39, A_40) | ~r1_tsep_1(A_40, B_39) | ~l1_struct_0(B_39) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.29  tff(c_80, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_45, c_77])).
% 2.31/1.29  tff(c_81, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_80])).
% 2.31/1.29  tff(c_89, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_81])).
% 2.31/1.29  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_89])).
% 2.31/1.29  tff(c_94, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 2.31/1.29  tff(c_96, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_94])).
% 2.31/1.29  tff(c_99, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_96])).
% 2.31/1.29  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_99])).
% 2.31/1.29  tff(c_105, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_94])).
% 2.31/1.29  tff(c_95, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 2.31/1.29  tff(c_111, plain, (![B_43, A_44]: (m1_subset_1(u1_struct_0(B_43), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.29  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.29  tff(c_115, plain, (![B_43, A_44]: (r1_tarski(u1_struct_0(B_43), u1_struct_0(A_44)) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_111, c_4])).
% 2.31/1.29  tff(c_118, plain, (![A_49, B_50]: (r1_xboole_0(u1_struct_0(A_49), u1_struct_0(B_50)) | ~r1_tsep_1(A_49, B_50) | ~l1_struct_0(B_50) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.29  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.29  tff(c_126, plain, (![A_51, B_52, A_53]: (r1_xboole_0(A_51, u1_struct_0(B_52)) | ~r1_tarski(A_51, u1_struct_0(A_53)) | ~r1_tsep_1(A_53, B_52) | ~l1_struct_0(B_52) | ~l1_struct_0(A_53))), inference(resolution, [status(thm)], [c_118, c_2])).
% 2.31/1.29  tff(c_130, plain, (![B_54, B_55, A_56]: (r1_xboole_0(u1_struct_0(B_54), u1_struct_0(B_55)) | ~r1_tsep_1(A_56, B_55) | ~l1_struct_0(B_55) | ~l1_struct_0(A_56) | ~m1_pre_topc(B_54, A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_115, c_126])).
% 2.31/1.29  tff(c_134, plain, (![B_54]: (r1_xboole_0(u1_struct_0(B_54), u1_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | ~m1_pre_topc(B_54, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_45, c_130])).
% 2.31/1.29  tff(c_151, plain, (![B_58]: (r1_xboole_0(u1_struct_0(B_58), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_58, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_95, c_105, c_134])).
% 2.31/1.29  tff(c_12, plain, (![A_10, B_12]: (r1_tsep_1(A_10, B_12) | ~r1_xboole_0(u1_struct_0(A_10), u1_struct_0(B_12)) | ~l1_struct_0(B_12) | ~l1_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.29  tff(c_154, plain, (![B_58]: (r1_tsep_1(B_58, '#skF_4') | ~l1_struct_0('#skF_4') | ~l1_struct_0(B_58) | ~m1_pre_topc(B_58, '#skF_3'))), inference(resolution, [status(thm)], [c_151, c_12])).
% 2.31/1.29  tff(c_172, plain, (![B_60]: (r1_tsep_1(B_60, '#skF_4') | ~l1_struct_0(B_60) | ~m1_pre_topc(B_60, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_154])).
% 2.31/1.29  tff(c_22, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.31/1.29  tff(c_44, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_22])).
% 2.31/1.29  tff(c_179, plain, (~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_172, c_44])).
% 2.31/1.29  tff(c_188, plain, (~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_179])).
% 2.31/1.29  tff(c_191, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_188])).
% 2.31/1.29  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_191])).
% 2.31/1.29  tff(c_197, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 2.31/1.29  tff(c_196, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.31/1.29  tff(c_230, plain, (![B_70, A_71]: (r1_tsep_1(B_70, A_71) | ~r1_tsep_1(A_71, B_70) | ~l1_struct_0(B_70) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.29  tff(c_232, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_196, c_230])).
% 2.31/1.29  tff(c_235, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_197, c_232])).
% 2.31/1.29  tff(c_236, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_235])).
% 2.31/1.29  tff(c_244, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_236])).
% 2.31/1.29  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_244])).
% 2.31/1.29  tff(c_249, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_235])).
% 2.31/1.29  tff(c_253, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_249])).
% 2.31/1.29  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_253])).
% 2.31/1.29  tff(c_258, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 2.31/1.29  tff(c_259, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 2.31/1.29  tff(c_293, plain, (![B_83, A_84]: (r1_tsep_1(B_83, A_84) | ~r1_tsep_1(A_84, B_83) | ~l1_struct_0(B_83) | ~l1_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.29  tff(c_297, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_259, c_293])).
% 2.31/1.29  tff(c_301, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_258, c_297])).
% 2.31/1.29  tff(c_302, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_301])).
% 2.31/1.29  tff(c_305, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_302])).
% 2.31/1.29  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_282, c_305])).
% 2.31/1.29  tff(c_310, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_301])).
% 2.31/1.29  tff(c_314, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_310])).
% 2.31/1.29  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_286, c_314])).
% 2.31/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  
% 2.31/1.29  Inference rules
% 2.31/1.29  ----------------------
% 2.31/1.29  #Ref     : 0
% 2.31/1.29  #Sup     : 44
% 2.31/1.29  #Fact    : 0
% 2.31/1.29  #Define  : 0
% 2.31/1.29  #Split   : 7
% 2.31/1.29  #Chain   : 0
% 2.31/1.29  #Close   : 0
% 2.31/1.29  
% 2.31/1.29  Ordering : KBO
% 2.31/1.29  
% 2.31/1.29  Simplification rules
% 2.31/1.29  ----------------------
% 2.31/1.29  #Subsume      : 0
% 2.31/1.29  #Demod        : 37
% 2.31/1.29  #Tautology    : 8
% 2.31/1.29  #SimpNegUnit  : 2
% 2.31/1.29  #BackRed      : 0
% 2.31/1.29  
% 2.31/1.29  #Partial instantiations: 0
% 2.31/1.29  #Strategies tried      : 1
% 2.31/1.29  
% 2.31/1.29  Timing (in seconds)
% 2.31/1.29  ----------------------
% 2.31/1.29  Preprocessing        : 0.29
% 2.31/1.29  Parsing              : 0.16
% 2.31/1.29  CNF conversion       : 0.02
% 2.31/1.29  Main loop            : 0.23
% 2.31/1.29  Inferencing          : 0.09
% 2.31/1.29  Reduction            : 0.06
% 2.31/1.29  Demodulation         : 0.04
% 2.31/1.29  BG Simplification    : 0.01
% 2.31/1.29  Subsumption          : 0.04
% 2.31/1.29  Abstraction          : 0.01
% 2.31/1.29  MUC search           : 0.00
% 2.31/1.29  Cooper               : 0.00
% 2.31/1.29  Total                : 0.56
% 2.31/1.29  Index Insertion      : 0.00
% 2.31/1.29  Index Deletion       : 0.00
% 2.31/1.29  Index Matching       : 0.00
% 2.31/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
