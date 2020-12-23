%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:20 EST 2020

% Result     : Theorem 9.01s
% Output     : CNFRefutation 9.01s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 284 expanded)
%              Number of leaves         :   34 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  278 (1238 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,C,D) )
                     => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r8_relat_2(A,B)
        <=> ! [C,D,E] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(E,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,E),A) )
             => r2_hidden(k4_tarski(C,E),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(c_56,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_168,plain,(
    ! [A_92] :
      ( m1_subset_1(u1_orders_2(A_92),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0(A_92))))
      | ~ l1_orders_2(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( v1_relat_1(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_174,plain,(
    ! [A_92] :
      ( v1_relat_1(u1_orders_2(A_92))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92) ) ),
    inference(resolution,[status(thm)],[c_168,c_14])).

tff(c_181,plain,(
    ! [A_92] :
      ( v1_relat_1(u1_orders_2(A_92))
      | ~ l1_orders_2(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_174])).

tff(c_262,plain,(
    ! [B_113,C_114,A_115] :
      ( r2_hidden(k4_tarski(B_113,C_114),u1_orders_2(A_115))
      | ~ r1_orders_2(A_115,B_113,C_114)
      | ~ m1_subset_1(C_114,u1_struct_0(A_115))
      | ~ m1_subset_1(B_113,u1_struct_0(A_115))
      | ~ l1_orders_2(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_334,plain,(
    ! [A_131,B_132,C_133] :
      ( ~ v1_xboole_0(u1_orders_2(A_131))
      | ~ r1_orders_2(A_131,B_132,C_133)
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l1_orders_2(A_131) ) ),
    inference(resolution,[status(thm)],[c_262,c_2])).

tff(c_336,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_334])).

tff(c_341,plain,(
    ~ v1_xboole_0(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_336])).

tff(c_66,plain,(
    ! [B_65,A_66] :
      ( v1_xboole_0(B_65)
      | ~ m1_subset_1(B_65,A_66)
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_76,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_66])).

tff(c_79,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_58,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_274,plain,(
    ! [B_113,C_114,A_115] :
      ( m1_subset_1(k4_tarski(B_113,C_114),u1_orders_2(A_115))
      | v1_xboole_0(u1_orders_2(A_115))
      | ~ r1_orders_2(A_115,B_113,C_114)
      | ~ m1_subset_1(C_114,u1_struct_0(A_115))
      | ~ m1_subset_1(B_113,u1_struct_0(A_115))
      | ~ l1_orders_2(A_115) ) ),
    inference(resolution,[status(thm)],[c_262,c_6])).

tff(c_36,plain,(
    ! [A_40] :
      ( r8_relat_2(u1_orders_2(A_40),u1_struct_0(A_40))
      | ~ v4_orders_2(A_40)
      | ~ l1_orders_2(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_345,plain,(
    ! [D_138,E_137,A_136,B_134,C_135] :
      ( r2_hidden(k4_tarski(C_135,E_137),A_136)
      | ~ r2_hidden(k4_tarski(D_138,E_137),A_136)
      | ~ r2_hidden(k4_tarski(C_135,D_138),A_136)
      | ~ r2_hidden(E_137,B_134)
      | ~ r2_hidden(D_138,B_134)
      | ~ r2_hidden(C_135,B_134)
      | ~ r8_relat_2(A_136,B_134)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_393,plain,(
    ! [C_159,D_158,A_162,B_160,E_161] :
      ( r2_hidden(k4_tarski(C_159,E_161),A_162)
      | ~ r2_hidden(k4_tarski(C_159,D_158),A_162)
      | ~ r2_hidden(E_161,B_160)
      | ~ r2_hidden(D_158,B_160)
      | ~ r2_hidden(C_159,B_160)
      | ~ r8_relat_2(A_162,B_160)
      | ~ v1_relat_1(A_162)
      | ~ m1_subset_1(k4_tarski(D_158,E_161),A_162)
      | v1_xboole_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_8,c_345])).

tff(c_411,plain,(
    ! [E_165,D_169,C_166,B_167,A_168] :
      ( r2_hidden(k4_tarski(C_166,E_165),A_168)
      | ~ r2_hidden(E_165,B_167)
      | ~ r2_hidden(D_169,B_167)
      | ~ r2_hidden(C_166,B_167)
      | ~ r8_relat_2(A_168,B_167)
      | ~ v1_relat_1(A_168)
      | ~ m1_subset_1(k4_tarski(D_169,E_165),A_168)
      | ~ m1_subset_1(k4_tarski(C_166,D_169),A_168)
      | v1_xboole_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_8,c_393])).

tff(c_452,plain,(
    ! [D_184,B_185,A_187,C_188,A_186] :
      ( r2_hidden(k4_tarski(C_188,B_185),A_187)
      | ~ r2_hidden(D_184,A_186)
      | ~ r2_hidden(C_188,A_186)
      | ~ r8_relat_2(A_187,A_186)
      | ~ v1_relat_1(A_187)
      | ~ m1_subset_1(k4_tarski(D_184,B_185),A_187)
      | ~ m1_subset_1(k4_tarski(C_188,D_184),A_187)
      | v1_xboole_0(A_187)
      | ~ m1_subset_1(B_185,A_186)
      | v1_xboole_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_8,c_411])).

tff(c_486,plain,(
    ! [C_195,A_194,B_197,A_196,B_193] :
      ( r2_hidden(k4_tarski(C_195,B_197),A_194)
      | ~ r2_hidden(C_195,A_196)
      | ~ r8_relat_2(A_194,A_196)
      | ~ v1_relat_1(A_194)
      | ~ m1_subset_1(k4_tarski(B_193,B_197),A_194)
      | ~ m1_subset_1(k4_tarski(C_195,B_193),A_194)
      | v1_xboole_0(A_194)
      | ~ m1_subset_1(B_197,A_196)
      | ~ m1_subset_1(B_193,A_196)
      | v1_xboole_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_8,c_452])).

tff(c_533,plain,(
    ! [B_208,A_209,B_210,A_206,B_207] :
      ( r2_hidden(k4_tarski(B_208,B_207),A_206)
      | ~ r8_relat_2(A_206,A_209)
      | ~ v1_relat_1(A_206)
      | ~ m1_subset_1(k4_tarski(B_210,B_207),A_206)
      | ~ m1_subset_1(k4_tarski(B_208,B_210),A_206)
      | v1_xboole_0(A_206)
      | ~ m1_subset_1(B_207,A_209)
      | ~ m1_subset_1(B_210,A_209)
      | ~ m1_subset_1(B_208,A_209)
      | v1_xboole_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_8,c_486])).

tff(c_3174,plain,(
    ! [B_510,B_511,A_512,B_513] :
      ( r2_hidden(k4_tarski(B_510,B_511),u1_orders_2(A_512))
      | ~ v1_relat_1(u1_orders_2(A_512))
      | ~ m1_subset_1(k4_tarski(B_513,B_511),u1_orders_2(A_512))
      | ~ m1_subset_1(k4_tarski(B_510,B_513),u1_orders_2(A_512))
      | v1_xboole_0(u1_orders_2(A_512))
      | ~ m1_subset_1(B_511,u1_struct_0(A_512))
      | ~ m1_subset_1(B_513,u1_struct_0(A_512))
      | ~ m1_subset_1(B_510,u1_struct_0(A_512))
      | v1_xboole_0(u1_struct_0(A_512))
      | ~ v4_orders_2(A_512)
      | ~ l1_orders_2(A_512) ) ),
    inference(resolution,[status(thm)],[c_36,c_533])).

tff(c_3239,plain,(
    ! [B_519,C_520,A_521,B_522] :
      ( r2_hidden(k4_tarski(B_519,C_520),u1_orders_2(A_521))
      | ~ v1_relat_1(u1_orders_2(A_521))
      | ~ m1_subset_1(k4_tarski(B_519,B_522),u1_orders_2(A_521))
      | ~ m1_subset_1(B_519,u1_struct_0(A_521))
      | v1_xboole_0(u1_struct_0(A_521))
      | ~ v4_orders_2(A_521)
      | v1_xboole_0(u1_orders_2(A_521))
      | ~ r1_orders_2(A_521,B_522,C_520)
      | ~ m1_subset_1(C_520,u1_struct_0(A_521))
      | ~ m1_subset_1(B_522,u1_struct_0(A_521))
      | ~ l1_orders_2(A_521) ) ),
    inference(resolution,[status(thm)],[c_274,c_3174])).

tff(c_3295,plain,(
    ! [B_523,C_524,A_525,C_526] :
      ( r2_hidden(k4_tarski(B_523,C_524),u1_orders_2(A_525))
      | ~ v1_relat_1(u1_orders_2(A_525))
      | v1_xboole_0(u1_struct_0(A_525))
      | ~ v4_orders_2(A_525)
      | ~ r1_orders_2(A_525,C_526,C_524)
      | ~ m1_subset_1(C_524,u1_struct_0(A_525))
      | v1_xboole_0(u1_orders_2(A_525))
      | ~ r1_orders_2(A_525,B_523,C_526)
      | ~ m1_subset_1(C_526,u1_struct_0(A_525))
      | ~ m1_subset_1(B_523,u1_struct_0(A_525))
      | ~ l1_orders_2(A_525) ) ),
    inference(resolution,[status(thm)],[c_274,c_3239])).

tff(c_3301,plain,(
    ! [B_523] :
      ( r2_hidden(k4_tarski(B_523,'#skF_7'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ v4_orders_2('#skF_5')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',B_523,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_523,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_3295])).

tff(c_3308,plain,(
    ! [B_523] :
      ( r2_hidden(k4_tarski(B_523,'#skF_7'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',B_523,'#skF_6')
      | ~ m1_subset_1(B_523,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_58,c_3301])).

tff(c_3309,plain,(
    ! [B_523] :
      ( r2_hidden(k4_tarski(B_523,'#skF_7'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',B_523,'#skF_6')
      | ~ m1_subset_1(B_523,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_79,c_3308])).

tff(c_3314,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3309])).

tff(c_3318,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_181,c_3314])).

tff(c_3322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3318])).

tff(c_3324,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3309])).

tff(c_46,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3303,plain,(
    ! [B_523] :
      ( r2_hidden(k4_tarski(B_523,'#skF_8'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ v4_orders_2('#skF_5')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',B_523,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_523,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_3295])).

tff(c_3312,plain,(
    ! [B_523] :
      ( r2_hidden(k4_tarski(B_523,'#skF_8'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',B_523,'#skF_7')
      | ~ m1_subset_1(B_523,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_58,c_3303])).

tff(c_3313,plain,(
    ! [B_523] :
      ( r2_hidden(k4_tarski(B_523,'#skF_8'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',B_523,'#skF_7')
      | ~ m1_subset_1(B_523,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_79,c_3312])).

tff(c_3656,plain,(
    ! [B_534] :
      ( r2_hidden(k4_tarski(B_534,'#skF_8'),u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',B_534,'#skF_7')
      | ~ m1_subset_1(B_534,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3324,c_3313])).

tff(c_38,plain,(
    ! [A_41,B_45,C_47] :
      ( r1_orders_2(A_41,B_45,C_47)
      | ~ r2_hidden(k4_tarski(B_45,C_47),u1_orders_2(A_41))
      | ~ m1_subset_1(C_47,u1_struct_0(A_41))
      | ~ m1_subset_1(B_45,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3691,plain,(
    ! [B_534] :
      ( r1_orders_2('#skF_5',B_534,'#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_orders_2('#skF_5',B_534,'#skF_7')
      | ~ m1_subset_1(B_534,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3656,c_38])).

tff(c_3736,plain,(
    ! [B_535] :
      ( r1_orders_2('#skF_5',B_535,'#skF_8')
      | ~ r1_orders_2('#skF_5',B_535,'#skF_7')
      | ~ m1_subset_1(B_535,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_3691])).

tff(c_3807,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_3736])).

tff(c_3865,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3807])).

tff(c_3867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_3865])).

tff(c_3869,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3968,plain,(
    ! [A_561] :
      ( m1_subset_1(u1_orders_2(A_561),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_561),u1_struct_0(A_561))))
      | ~ l1_orders_2(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_18,plain,(
    ! [C_15,A_12,B_13] :
      ( v1_xboole_0(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3998,plain,(
    ! [A_567] :
      ( v1_xboole_0(u1_orders_2(A_567))
      | ~ v1_xboole_0(u1_struct_0(A_567))
      | ~ l1_orders_2(A_567) ) ),
    inference(resolution,[status(thm)],[c_3968,c_18])).

tff(c_4001,plain,
    ( v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_3869,c_3998])).

tff(c_4004,plain,(
    v1_xboole_0(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4001])).

tff(c_4089,plain,(
    ! [B_584,C_585,A_586] :
      ( r2_hidden(k4_tarski(B_584,C_585),u1_orders_2(A_586))
      | ~ r1_orders_2(A_586,B_584,C_585)
      | ~ m1_subset_1(C_585,u1_struct_0(A_586))
      | ~ m1_subset_1(B_584,u1_struct_0(A_586))
      | ~ l1_orders_2(A_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4146,plain,(
    ! [A_600,B_601,C_602] :
      ( ~ v1_xboole_0(u1_orders_2(A_600))
      | ~ r1_orders_2(A_600,B_601,C_602)
      | ~ m1_subset_1(C_602,u1_struct_0(A_600))
      | ~ m1_subset_1(B_601,u1_struct_0(A_600))
      | ~ l1_orders_2(A_600) ) ),
    inference(resolution,[status(thm)],[c_4089,c_2])).

tff(c_4148,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_4146])).

tff(c_4154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_4004,c_4148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.01/3.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.01/3.45  
% 9.01/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.01/3.45  %$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 9.01/3.45  
% 9.01/3.45  %Foreground sorts:
% 9.01/3.45  
% 9.01/3.45  
% 9.01/3.45  %Background operators:
% 9.01/3.45  
% 9.01/3.45  
% 9.01/3.45  %Foreground operators:
% 9.01/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.01/3.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.01/3.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.01/3.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.01/3.45  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.01/3.45  tff('#skF_7', type, '#skF_7': $i).
% 9.01/3.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.01/3.45  tff('#skF_5', type, '#skF_5': $i).
% 9.01/3.45  tff('#skF_6', type, '#skF_6': $i).
% 9.01/3.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.01/3.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.01/3.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.01/3.45  tff('#skF_8', type, '#skF_8': $i).
% 9.01/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.01/3.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.01/3.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.01/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.01/3.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.01/3.45  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 9.01/3.45  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 9.01/3.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.01/3.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.01/3.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.01/3.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.01/3.45  
% 9.01/3.47  tff(f_120, negated_conjecture, ~(![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 9.01/3.47  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.01/3.47  tff(f_100, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 9.01/3.47  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.01/3.47  tff(f_96, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 9.01/3.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.01/3.47  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.01/3.47  tff(f_84, axiom, (![A]: (l1_orders_2(A) => (v4_orders_2(A) <=> r8_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_orders_2)).
% 9.01/3.47  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (r8_relat_2(A, B) <=> (![C, D, E]: (((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(E, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, E), A)) => r2_hidden(k4_tarski(C, E), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_2)).
% 9.01/3.47  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 9.01/3.47  tff(c_56, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.01/3.47  tff(c_54, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.01/3.47  tff(c_52, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.01/3.47  tff(c_44, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.01/3.47  tff(c_48, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.01/3.47  tff(c_50, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.01/3.47  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.01/3.47  tff(c_168, plain, (![A_92]: (m1_subset_1(u1_orders_2(A_92), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0(A_92)))) | ~l1_orders_2(A_92))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.01/3.47  tff(c_14, plain, (![B_9, A_7]: (v1_relat_1(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.01/3.47  tff(c_174, plain, (![A_92]: (v1_relat_1(u1_orders_2(A_92)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0(A_92))) | ~l1_orders_2(A_92))), inference(resolution, [status(thm)], [c_168, c_14])).
% 9.01/3.47  tff(c_181, plain, (![A_92]: (v1_relat_1(u1_orders_2(A_92)) | ~l1_orders_2(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_174])).
% 9.01/3.47  tff(c_262, plain, (![B_113, C_114, A_115]: (r2_hidden(k4_tarski(B_113, C_114), u1_orders_2(A_115)) | ~r1_orders_2(A_115, B_113, C_114) | ~m1_subset_1(C_114, u1_struct_0(A_115)) | ~m1_subset_1(B_113, u1_struct_0(A_115)) | ~l1_orders_2(A_115))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.01/3.47  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.01/3.47  tff(c_334, plain, (![A_131, B_132, C_133]: (~v1_xboole_0(u1_orders_2(A_131)) | ~r1_orders_2(A_131, B_132, C_133) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l1_orders_2(A_131))), inference(resolution, [status(thm)], [c_262, c_2])).
% 9.01/3.47  tff(c_336, plain, (~v1_xboole_0(u1_orders_2('#skF_5')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_48, c_334])).
% 9.01/3.47  tff(c_341, plain, (~v1_xboole_0(u1_orders_2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_336])).
% 9.01/3.47  tff(c_66, plain, (![B_65, A_66]: (v1_xboole_0(B_65) | ~m1_subset_1(B_65, A_66) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.01/3.47  tff(c_76, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_66])).
% 9.01/3.47  tff(c_79, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_76])).
% 9.01/3.47  tff(c_58, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.01/3.47  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.01/3.47  tff(c_274, plain, (![B_113, C_114, A_115]: (m1_subset_1(k4_tarski(B_113, C_114), u1_orders_2(A_115)) | v1_xboole_0(u1_orders_2(A_115)) | ~r1_orders_2(A_115, B_113, C_114) | ~m1_subset_1(C_114, u1_struct_0(A_115)) | ~m1_subset_1(B_113, u1_struct_0(A_115)) | ~l1_orders_2(A_115))), inference(resolution, [status(thm)], [c_262, c_6])).
% 9.01/3.47  tff(c_36, plain, (![A_40]: (r8_relat_2(u1_orders_2(A_40), u1_struct_0(A_40)) | ~v4_orders_2(A_40) | ~l1_orders_2(A_40))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.01/3.47  tff(c_8, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.01/3.47  tff(c_345, plain, (![D_138, E_137, A_136, B_134, C_135]: (r2_hidden(k4_tarski(C_135, E_137), A_136) | ~r2_hidden(k4_tarski(D_138, E_137), A_136) | ~r2_hidden(k4_tarski(C_135, D_138), A_136) | ~r2_hidden(E_137, B_134) | ~r2_hidden(D_138, B_134) | ~r2_hidden(C_135, B_134) | ~r8_relat_2(A_136, B_134) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.01/3.47  tff(c_393, plain, (![C_159, D_158, A_162, B_160, E_161]: (r2_hidden(k4_tarski(C_159, E_161), A_162) | ~r2_hidden(k4_tarski(C_159, D_158), A_162) | ~r2_hidden(E_161, B_160) | ~r2_hidden(D_158, B_160) | ~r2_hidden(C_159, B_160) | ~r8_relat_2(A_162, B_160) | ~v1_relat_1(A_162) | ~m1_subset_1(k4_tarski(D_158, E_161), A_162) | v1_xboole_0(A_162))), inference(resolution, [status(thm)], [c_8, c_345])).
% 9.01/3.47  tff(c_411, plain, (![E_165, D_169, C_166, B_167, A_168]: (r2_hidden(k4_tarski(C_166, E_165), A_168) | ~r2_hidden(E_165, B_167) | ~r2_hidden(D_169, B_167) | ~r2_hidden(C_166, B_167) | ~r8_relat_2(A_168, B_167) | ~v1_relat_1(A_168) | ~m1_subset_1(k4_tarski(D_169, E_165), A_168) | ~m1_subset_1(k4_tarski(C_166, D_169), A_168) | v1_xboole_0(A_168))), inference(resolution, [status(thm)], [c_8, c_393])).
% 9.01/3.47  tff(c_452, plain, (![D_184, B_185, A_187, C_188, A_186]: (r2_hidden(k4_tarski(C_188, B_185), A_187) | ~r2_hidden(D_184, A_186) | ~r2_hidden(C_188, A_186) | ~r8_relat_2(A_187, A_186) | ~v1_relat_1(A_187) | ~m1_subset_1(k4_tarski(D_184, B_185), A_187) | ~m1_subset_1(k4_tarski(C_188, D_184), A_187) | v1_xboole_0(A_187) | ~m1_subset_1(B_185, A_186) | v1_xboole_0(A_186))), inference(resolution, [status(thm)], [c_8, c_411])).
% 9.01/3.47  tff(c_486, plain, (![C_195, A_194, B_197, A_196, B_193]: (r2_hidden(k4_tarski(C_195, B_197), A_194) | ~r2_hidden(C_195, A_196) | ~r8_relat_2(A_194, A_196) | ~v1_relat_1(A_194) | ~m1_subset_1(k4_tarski(B_193, B_197), A_194) | ~m1_subset_1(k4_tarski(C_195, B_193), A_194) | v1_xboole_0(A_194) | ~m1_subset_1(B_197, A_196) | ~m1_subset_1(B_193, A_196) | v1_xboole_0(A_196))), inference(resolution, [status(thm)], [c_8, c_452])).
% 9.01/3.47  tff(c_533, plain, (![B_208, A_209, B_210, A_206, B_207]: (r2_hidden(k4_tarski(B_208, B_207), A_206) | ~r8_relat_2(A_206, A_209) | ~v1_relat_1(A_206) | ~m1_subset_1(k4_tarski(B_210, B_207), A_206) | ~m1_subset_1(k4_tarski(B_208, B_210), A_206) | v1_xboole_0(A_206) | ~m1_subset_1(B_207, A_209) | ~m1_subset_1(B_210, A_209) | ~m1_subset_1(B_208, A_209) | v1_xboole_0(A_209))), inference(resolution, [status(thm)], [c_8, c_486])).
% 9.01/3.47  tff(c_3174, plain, (![B_510, B_511, A_512, B_513]: (r2_hidden(k4_tarski(B_510, B_511), u1_orders_2(A_512)) | ~v1_relat_1(u1_orders_2(A_512)) | ~m1_subset_1(k4_tarski(B_513, B_511), u1_orders_2(A_512)) | ~m1_subset_1(k4_tarski(B_510, B_513), u1_orders_2(A_512)) | v1_xboole_0(u1_orders_2(A_512)) | ~m1_subset_1(B_511, u1_struct_0(A_512)) | ~m1_subset_1(B_513, u1_struct_0(A_512)) | ~m1_subset_1(B_510, u1_struct_0(A_512)) | v1_xboole_0(u1_struct_0(A_512)) | ~v4_orders_2(A_512) | ~l1_orders_2(A_512))), inference(resolution, [status(thm)], [c_36, c_533])).
% 9.01/3.47  tff(c_3239, plain, (![B_519, C_520, A_521, B_522]: (r2_hidden(k4_tarski(B_519, C_520), u1_orders_2(A_521)) | ~v1_relat_1(u1_orders_2(A_521)) | ~m1_subset_1(k4_tarski(B_519, B_522), u1_orders_2(A_521)) | ~m1_subset_1(B_519, u1_struct_0(A_521)) | v1_xboole_0(u1_struct_0(A_521)) | ~v4_orders_2(A_521) | v1_xboole_0(u1_orders_2(A_521)) | ~r1_orders_2(A_521, B_522, C_520) | ~m1_subset_1(C_520, u1_struct_0(A_521)) | ~m1_subset_1(B_522, u1_struct_0(A_521)) | ~l1_orders_2(A_521))), inference(resolution, [status(thm)], [c_274, c_3174])).
% 9.01/3.47  tff(c_3295, plain, (![B_523, C_524, A_525, C_526]: (r2_hidden(k4_tarski(B_523, C_524), u1_orders_2(A_525)) | ~v1_relat_1(u1_orders_2(A_525)) | v1_xboole_0(u1_struct_0(A_525)) | ~v4_orders_2(A_525) | ~r1_orders_2(A_525, C_526, C_524) | ~m1_subset_1(C_524, u1_struct_0(A_525)) | v1_xboole_0(u1_orders_2(A_525)) | ~r1_orders_2(A_525, B_523, C_526) | ~m1_subset_1(C_526, u1_struct_0(A_525)) | ~m1_subset_1(B_523, u1_struct_0(A_525)) | ~l1_orders_2(A_525))), inference(resolution, [status(thm)], [c_274, c_3239])).
% 9.01/3.47  tff(c_3301, plain, (![B_523]: (r2_hidden(k4_tarski(B_523, '#skF_7'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~v4_orders_2('#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | v1_xboole_0(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', B_523, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(B_523, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_3295])).
% 9.01/3.47  tff(c_3308, plain, (![B_523]: (r2_hidden(k4_tarski(B_523, '#skF_7'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', B_523, '#skF_6') | ~m1_subset_1(B_523, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_58, c_3301])).
% 9.01/3.47  tff(c_3309, plain, (![B_523]: (r2_hidden(k4_tarski(B_523, '#skF_7'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', B_523, '#skF_6') | ~m1_subset_1(B_523, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_341, c_79, c_3308])).
% 9.01/3.47  tff(c_3314, plain, (~v1_relat_1(u1_orders_2('#skF_5'))), inference(splitLeft, [status(thm)], [c_3309])).
% 9.01/3.47  tff(c_3318, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_181, c_3314])).
% 9.01/3.47  tff(c_3322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3318])).
% 9.01/3.47  tff(c_3324, plain, (v1_relat_1(u1_orders_2('#skF_5'))), inference(splitRight, [status(thm)], [c_3309])).
% 9.01/3.47  tff(c_46, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.01/3.47  tff(c_3303, plain, (![B_523]: (r2_hidden(k4_tarski(B_523, '#skF_8'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~v4_orders_2('#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v1_xboole_0(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', B_523, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1(B_523, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_3295])).
% 9.01/3.47  tff(c_3312, plain, (![B_523]: (r2_hidden(k4_tarski(B_523, '#skF_8'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', B_523, '#skF_7') | ~m1_subset_1(B_523, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_58, c_3303])).
% 9.01/3.47  tff(c_3313, plain, (![B_523]: (r2_hidden(k4_tarski(B_523, '#skF_8'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', B_523, '#skF_7') | ~m1_subset_1(B_523, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_341, c_79, c_3312])).
% 9.01/3.47  tff(c_3656, plain, (![B_534]: (r2_hidden(k4_tarski(B_534, '#skF_8'), u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', B_534, '#skF_7') | ~m1_subset_1(B_534, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_3324, c_3313])).
% 9.01/3.47  tff(c_38, plain, (![A_41, B_45, C_47]: (r1_orders_2(A_41, B_45, C_47) | ~r2_hidden(k4_tarski(B_45, C_47), u1_orders_2(A_41)) | ~m1_subset_1(C_47, u1_struct_0(A_41)) | ~m1_subset_1(B_45, u1_struct_0(A_41)) | ~l1_orders_2(A_41))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.01/3.47  tff(c_3691, plain, (![B_534]: (r1_orders_2('#skF_5', B_534, '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~r1_orders_2('#skF_5', B_534, '#skF_7') | ~m1_subset_1(B_534, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_3656, c_38])).
% 9.01/3.47  tff(c_3736, plain, (![B_535]: (r1_orders_2('#skF_5', B_535, '#skF_8') | ~r1_orders_2('#skF_5', B_535, '#skF_7') | ~m1_subset_1(B_535, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_3691])).
% 9.01/3.47  tff(c_3807, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_8') | ~r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_3736])).
% 9.01/3.47  tff(c_3865, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3807])).
% 9.01/3.47  tff(c_3867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_3865])).
% 9.01/3.47  tff(c_3869, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_76])).
% 9.01/3.47  tff(c_3968, plain, (![A_561]: (m1_subset_1(u1_orders_2(A_561), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_561), u1_struct_0(A_561)))) | ~l1_orders_2(A_561))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.01/3.47  tff(c_18, plain, (![C_15, A_12, B_13]: (v1_xboole_0(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.01/3.47  tff(c_3998, plain, (![A_567]: (v1_xboole_0(u1_orders_2(A_567)) | ~v1_xboole_0(u1_struct_0(A_567)) | ~l1_orders_2(A_567))), inference(resolution, [status(thm)], [c_3968, c_18])).
% 9.01/3.47  tff(c_4001, plain, (v1_xboole_0(u1_orders_2('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_3869, c_3998])).
% 9.01/3.47  tff(c_4004, plain, (v1_xboole_0(u1_orders_2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4001])).
% 9.01/3.47  tff(c_4089, plain, (![B_584, C_585, A_586]: (r2_hidden(k4_tarski(B_584, C_585), u1_orders_2(A_586)) | ~r1_orders_2(A_586, B_584, C_585) | ~m1_subset_1(C_585, u1_struct_0(A_586)) | ~m1_subset_1(B_584, u1_struct_0(A_586)) | ~l1_orders_2(A_586))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.01/3.47  tff(c_4146, plain, (![A_600, B_601, C_602]: (~v1_xboole_0(u1_orders_2(A_600)) | ~r1_orders_2(A_600, B_601, C_602) | ~m1_subset_1(C_602, u1_struct_0(A_600)) | ~m1_subset_1(B_601, u1_struct_0(A_600)) | ~l1_orders_2(A_600))), inference(resolution, [status(thm)], [c_4089, c_2])).
% 9.01/3.47  tff(c_4148, plain, (~v1_xboole_0(u1_orders_2('#skF_5')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_48, c_4146])).
% 9.01/3.47  tff(c_4154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_4004, c_4148])).
% 9.01/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.01/3.47  
% 9.01/3.47  Inference rules
% 9.01/3.47  ----------------------
% 9.01/3.47  #Ref     : 0
% 9.01/3.47  #Sup     : 1047
% 9.01/3.47  #Fact    : 0
% 9.01/3.47  #Define  : 0
% 9.01/3.47  #Split   : 8
% 9.01/3.47  #Chain   : 0
% 9.01/3.47  #Close   : 0
% 9.01/3.47  
% 9.01/3.47  Ordering : KBO
% 9.01/3.47  
% 9.01/3.47  Simplification rules
% 9.01/3.47  ----------------------
% 9.01/3.47  #Subsume      : 78
% 9.01/3.47  #Demod        : 64
% 9.01/3.47  #Tautology    : 79
% 9.01/3.47  #SimpNegUnit  : 67
% 9.01/3.47  #BackRed      : 0
% 9.01/3.47  
% 9.01/3.47  #Partial instantiations: 0
% 9.01/3.47  #Strategies tried      : 1
% 9.01/3.47  
% 9.01/3.47  Timing (in seconds)
% 9.01/3.47  ----------------------
% 9.01/3.47  Preprocessing        : 0.37
% 9.01/3.47  Parsing              : 0.19
% 9.01/3.47  CNF conversion       : 0.03
% 9.01/3.48  Main loop            : 2.21
% 9.01/3.48  Inferencing          : 0.43
% 9.01/3.48  Reduction            : 0.33
% 9.01/3.48  Demodulation         : 0.21
% 9.01/3.48  BG Simplification    : 0.06
% 9.01/3.48  Subsumption          : 1.27
% 9.01/3.48  Abstraction          : 0.07
% 9.01/3.48  MUC search           : 0.00
% 9.01/3.48  Cooper               : 0.00
% 9.01/3.48  Total                : 2.63
% 9.01/3.48  Index Insertion      : 0.00
% 9.01/3.48  Index Deletion       : 0.00
% 9.01/3.48  Index Matching       : 0.00
% 9.01/3.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
