%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:19 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 104 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  175 ( 324 expanded)
%              Number of equality atoms :   11 (  25 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( r1_orders_2(A,B,C)
                    & r1_orders_2(A,C,B) )
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r4_relat_2(A,B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,C),A) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_52,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_156,plain,(
    ! [A_78] :
      ( m1_subset_1(u1_orders_2(A_78),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78),u1_struct_0(A_78))))
      | ~ l1_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( v1_relat_1(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_162,plain,(
    ! [A_78] :
      ( v1_relat_1(u1_orders_2(A_78))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_78),u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78) ) ),
    inference(resolution,[status(thm)],[c_156,c_14])).

tff(c_169,plain,(
    ! [A_78] :
      ( v1_relat_1(u1_orders_2(A_78))
      | ~ l1_orders_2(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_162])).

tff(c_62,plain,(
    ! [B_51,A_52] :
      ( v1_xboole_0(B_51)
      | ~ m1_subset_1(B_51,A_52)
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_69,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_62])).

tff(c_71,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_42,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_54,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_44,plain,(
    r1_orders_2('#skF_4','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    ! [A_33] :
      ( r4_relat_2(u1_orders_2(A_33),u1_struct_0(A_33))
      | ~ v5_orders_2(A_33)
      | ~ l1_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    ! [B_38,C_40,A_34] :
      ( r2_hidden(k4_tarski(B_38,C_40),u1_orders_2(A_34))
      | ~ r1_orders_2(A_34,B_38,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_305,plain,(
    ! [D_123,C_124,A_125,B_126] :
      ( D_123 = C_124
      | ~ r2_hidden(k4_tarski(D_123,C_124),A_125)
      | ~ r2_hidden(k4_tarski(C_124,D_123),A_125)
      | ~ r2_hidden(D_123,B_126)
      | ~ r2_hidden(C_124,B_126)
      | ~ r4_relat_2(A_125,B_126)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_510,plain,(
    ! [C_185,B_186,A_187,B_188] :
      ( C_185 = B_186
      | ~ r2_hidden(k4_tarski(C_185,B_186),u1_orders_2(A_187))
      | ~ r2_hidden(B_186,B_188)
      | ~ r2_hidden(C_185,B_188)
      | ~ r4_relat_2(u1_orders_2(A_187),B_188)
      | ~ v1_relat_1(u1_orders_2(A_187))
      | ~ r1_orders_2(A_187,B_186,C_185)
      | ~ m1_subset_1(C_185,u1_struct_0(A_187))
      | ~ m1_subset_1(B_186,u1_struct_0(A_187))
      | ~ l1_orders_2(A_187) ) ),
    inference(resolution,[status(thm)],[c_38,c_305])).

tff(c_526,plain,(
    ! [C_189,B_190,B_191,A_192] :
      ( C_189 = B_190
      | ~ r2_hidden(C_189,B_191)
      | ~ r2_hidden(B_190,B_191)
      | ~ r4_relat_2(u1_orders_2(A_192),B_191)
      | ~ v1_relat_1(u1_orders_2(A_192))
      | ~ r1_orders_2(A_192,C_189,B_190)
      | ~ r1_orders_2(A_192,B_190,C_189)
      | ~ m1_subset_1(C_189,u1_struct_0(A_192))
      | ~ m1_subset_1(B_190,u1_struct_0(A_192))
      | ~ l1_orders_2(A_192) ) ),
    inference(resolution,[status(thm)],[c_38,c_510])).

tff(c_560,plain,(
    ! [B_198,B_197,A_199,A_200] :
      ( B_198 = B_197
      | ~ r2_hidden(B_198,A_199)
      | ~ r4_relat_2(u1_orders_2(A_200),A_199)
      | ~ v1_relat_1(u1_orders_2(A_200))
      | ~ r1_orders_2(A_200,B_197,B_198)
      | ~ r1_orders_2(A_200,B_198,B_197)
      | ~ m1_subset_1(B_197,u1_struct_0(A_200))
      | ~ m1_subset_1(B_198,u1_struct_0(A_200))
      | ~ l1_orders_2(A_200)
      | ~ m1_subset_1(B_197,A_199)
      | v1_xboole_0(A_199) ) ),
    inference(resolution,[status(thm)],[c_8,c_526])).

tff(c_594,plain,(
    ! [B_206,B_205,A_207,A_208] :
      ( B_206 = B_205
      | ~ r4_relat_2(u1_orders_2(A_207),A_208)
      | ~ v1_relat_1(u1_orders_2(A_207))
      | ~ r1_orders_2(A_207,B_206,B_205)
      | ~ r1_orders_2(A_207,B_205,B_206)
      | ~ m1_subset_1(B_206,u1_struct_0(A_207))
      | ~ m1_subset_1(B_205,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207)
      | ~ m1_subset_1(B_206,A_208)
      | ~ m1_subset_1(B_205,A_208)
      | v1_xboole_0(A_208) ) ),
    inference(resolution,[status(thm)],[c_8,c_560])).

tff(c_610,plain,(
    ! [B_210,B_209,A_211] :
      ( B_210 = B_209
      | ~ v1_relat_1(u1_orders_2(A_211))
      | ~ r1_orders_2(A_211,B_209,B_210)
      | ~ r1_orders_2(A_211,B_210,B_209)
      | ~ m1_subset_1(B_209,u1_struct_0(A_211))
      | ~ m1_subset_1(B_210,u1_struct_0(A_211))
      | v1_xboole_0(u1_struct_0(A_211))
      | ~ v5_orders_2(A_211)
      | ~ l1_orders_2(A_211) ) ),
    inference(resolution,[status(thm)],[c_34,c_594])).

tff(c_616,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ v5_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_610])).

tff(c_623,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_50,c_48,c_46,c_616])).

tff(c_624,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_42,c_623])).

tff(c_631,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_624])).

tff(c_635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_631])).

tff(c_637,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_730,plain,(
    ! [A_237] :
      ( m1_subset_1(u1_orders_2(A_237),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_237),u1_struct_0(A_237))))
      | ~ l1_orders_2(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    ! [C_15,B_13,A_12] :
      ( v1_xboole_0(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(B_13,A_12)))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_746,plain,(
    ! [A_239] :
      ( v1_xboole_0(u1_orders_2(A_239))
      | ~ v1_xboole_0(u1_struct_0(A_239))
      | ~ l1_orders_2(A_239) ) ),
    inference(resolution,[status(thm)],[c_730,c_18])).

tff(c_749,plain,
    ( v1_xboole_0(u1_orders_2('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_637,c_746])).

tff(c_752,plain,(
    v1_xboole_0(u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_749])).

tff(c_815,plain,(
    ! [B_254,C_255,A_256] :
      ( r2_hidden(k4_tarski(B_254,C_255),u1_orders_2(A_256))
      | ~ r1_orders_2(A_256,B_254,C_255)
      | ~ m1_subset_1(C_255,u1_struct_0(A_256))
      | ~ m1_subset_1(B_254,u1_struct_0(A_256))
      | ~ l1_orders_2(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_856,plain,(
    ! [A_265,B_266,C_267] :
      ( ~ v1_xboole_0(u1_orders_2(A_265))
      | ~ r1_orders_2(A_265,B_266,C_267)
      | ~ m1_subset_1(C_267,u1_struct_0(A_265))
      | ~ m1_subset_1(B_266,u1_struct_0(A_265))
      | ~ l1_orders_2(A_265) ) ),
    inference(resolution,[status(thm)],[c_815,c_2])).

tff(c_858,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_856])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_50,c_752,c_858])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:06:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.60  
% 3.47/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.60  %$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.47/1.60  
% 3.47/1.60  %Foreground sorts:
% 3.47/1.60  
% 3.47/1.60  
% 3.47/1.60  %Background operators:
% 3.47/1.60  
% 3.47/1.60  
% 3.47/1.60  %Foreground operators:
% 3.47/1.60  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 3.47/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.47/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.47/1.60  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.47/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.47/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.47/1.60  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.47/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.60  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.47/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.60  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.47/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.47/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.60  
% 3.47/1.62  tff(f_115, negated_conjecture, ~(![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_orders_2)).
% 3.47/1.62  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.47/1.62  tff(f_98, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 3.47/1.62  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.47/1.62  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.47/1.62  tff(f_82, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_orders_2)).
% 3.47/1.62  tff(f_94, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 3.47/1.62  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (r4_relat_2(A, B) <=> (![C, D]: ((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, C), A)) => (C = D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_2)).
% 3.47/1.62  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.47/1.62  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.47/1.62  tff(c_52, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.62  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.62  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.62  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.47/1.62  tff(c_156, plain, (![A_78]: (m1_subset_1(u1_orders_2(A_78), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78), u1_struct_0(A_78)))) | ~l1_orders_2(A_78))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.47/1.62  tff(c_14, plain, (![B_9, A_7]: (v1_relat_1(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.47/1.62  tff(c_162, plain, (![A_78]: (v1_relat_1(u1_orders_2(A_78)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_78), u1_struct_0(A_78))) | ~l1_orders_2(A_78))), inference(resolution, [status(thm)], [c_156, c_14])).
% 3.47/1.62  tff(c_169, plain, (![A_78]: (v1_relat_1(u1_orders_2(A_78)) | ~l1_orders_2(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_162])).
% 3.47/1.62  tff(c_62, plain, (![B_51, A_52]: (v1_xboole_0(B_51) | ~m1_subset_1(B_51, A_52) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.47/1.62  tff(c_69, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_62])).
% 3.47/1.62  tff(c_71, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_69])).
% 3.47/1.62  tff(c_42, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.62  tff(c_54, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.62  tff(c_46, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.62  tff(c_44, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.62  tff(c_34, plain, (![A_33]: (r4_relat_2(u1_orders_2(A_33), u1_struct_0(A_33)) | ~v5_orders_2(A_33) | ~l1_orders_2(A_33))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.47/1.62  tff(c_8, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.47/1.62  tff(c_38, plain, (![B_38, C_40, A_34]: (r2_hidden(k4_tarski(B_38, C_40), u1_orders_2(A_34)) | ~r1_orders_2(A_34, B_38, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.47/1.62  tff(c_305, plain, (![D_123, C_124, A_125, B_126]: (D_123=C_124 | ~r2_hidden(k4_tarski(D_123, C_124), A_125) | ~r2_hidden(k4_tarski(C_124, D_123), A_125) | ~r2_hidden(D_123, B_126) | ~r2_hidden(C_124, B_126) | ~r4_relat_2(A_125, B_126) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.47/1.62  tff(c_510, plain, (![C_185, B_186, A_187, B_188]: (C_185=B_186 | ~r2_hidden(k4_tarski(C_185, B_186), u1_orders_2(A_187)) | ~r2_hidden(B_186, B_188) | ~r2_hidden(C_185, B_188) | ~r4_relat_2(u1_orders_2(A_187), B_188) | ~v1_relat_1(u1_orders_2(A_187)) | ~r1_orders_2(A_187, B_186, C_185) | ~m1_subset_1(C_185, u1_struct_0(A_187)) | ~m1_subset_1(B_186, u1_struct_0(A_187)) | ~l1_orders_2(A_187))), inference(resolution, [status(thm)], [c_38, c_305])).
% 3.47/1.62  tff(c_526, plain, (![C_189, B_190, B_191, A_192]: (C_189=B_190 | ~r2_hidden(C_189, B_191) | ~r2_hidden(B_190, B_191) | ~r4_relat_2(u1_orders_2(A_192), B_191) | ~v1_relat_1(u1_orders_2(A_192)) | ~r1_orders_2(A_192, C_189, B_190) | ~r1_orders_2(A_192, B_190, C_189) | ~m1_subset_1(C_189, u1_struct_0(A_192)) | ~m1_subset_1(B_190, u1_struct_0(A_192)) | ~l1_orders_2(A_192))), inference(resolution, [status(thm)], [c_38, c_510])).
% 3.47/1.62  tff(c_560, plain, (![B_198, B_197, A_199, A_200]: (B_198=B_197 | ~r2_hidden(B_198, A_199) | ~r4_relat_2(u1_orders_2(A_200), A_199) | ~v1_relat_1(u1_orders_2(A_200)) | ~r1_orders_2(A_200, B_197, B_198) | ~r1_orders_2(A_200, B_198, B_197) | ~m1_subset_1(B_197, u1_struct_0(A_200)) | ~m1_subset_1(B_198, u1_struct_0(A_200)) | ~l1_orders_2(A_200) | ~m1_subset_1(B_197, A_199) | v1_xboole_0(A_199))), inference(resolution, [status(thm)], [c_8, c_526])).
% 3.47/1.62  tff(c_594, plain, (![B_206, B_205, A_207, A_208]: (B_206=B_205 | ~r4_relat_2(u1_orders_2(A_207), A_208) | ~v1_relat_1(u1_orders_2(A_207)) | ~r1_orders_2(A_207, B_206, B_205) | ~r1_orders_2(A_207, B_205, B_206) | ~m1_subset_1(B_206, u1_struct_0(A_207)) | ~m1_subset_1(B_205, u1_struct_0(A_207)) | ~l1_orders_2(A_207) | ~m1_subset_1(B_206, A_208) | ~m1_subset_1(B_205, A_208) | v1_xboole_0(A_208))), inference(resolution, [status(thm)], [c_8, c_560])).
% 3.47/1.62  tff(c_610, plain, (![B_210, B_209, A_211]: (B_210=B_209 | ~v1_relat_1(u1_orders_2(A_211)) | ~r1_orders_2(A_211, B_209, B_210) | ~r1_orders_2(A_211, B_210, B_209) | ~m1_subset_1(B_209, u1_struct_0(A_211)) | ~m1_subset_1(B_210, u1_struct_0(A_211)) | v1_xboole_0(u1_struct_0(A_211)) | ~v5_orders_2(A_211) | ~l1_orders_2(A_211))), inference(resolution, [status(thm)], [c_34, c_594])).
% 3.47/1.62  tff(c_616, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~v5_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_44, c_610])).
% 3.47/1.62  tff(c_623, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_50, c_48, c_46, c_616])).
% 3.47/1.62  tff(c_624, plain, (~v1_relat_1(u1_orders_2('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_71, c_42, c_623])).
% 3.47/1.62  tff(c_631, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_169, c_624])).
% 3.47/1.62  tff(c_635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_631])).
% 3.47/1.62  tff(c_637, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_69])).
% 3.47/1.62  tff(c_730, plain, (![A_237]: (m1_subset_1(u1_orders_2(A_237), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_237), u1_struct_0(A_237)))) | ~l1_orders_2(A_237))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.47/1.62  tff(c_18, plain, (![C_15, B_13, A_12]: (v1_xboole_0(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(B_13, A_12))) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.47/1.62  tff(c_746, plain, (![A_239]: (v1_xboole_0(u1_orders_2(A_239)) | ~v1_xboole_0(u1_struct_0(A_239)) | ~l1_orders_2(A_239))), inference(resolution, [status(thm)], [c_730, c_18])).
% 3.47/1.62  tff(c_749, plain, (v1_xboole_0(u1_orders_2('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_637, c_746])).
% 3.47/1.62  tff(c_752, plain, (v1_xboole_0(u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_749])).
% 3.47/1.62  tff(c_815, plain, (![B_254, C_255, A_256]: (r2_hidden(k4_tarski(B_254, C_255), u1_orders_2(A_256)) | ~r1_orders_2(A_256, B_254, C_255) | ~m1_subset_1(C_255, u1_struct_0(A_256)) | ~m1_subset_1(B_254, u1_struct_0(A_256)) | ~l1_orders_2(A_256))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.47/1.62  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.47/1.62  tff(c_856, plain, (![A_265, B_266, C_267]: (~v1_xboole_0(u1_orders_2(A_265)) | ~r1_orders_2(A_265, B_266, C_267) | ~m1_subset_1(C_267, u1_struct_0(A_265)) | ~m1_subset_1(B_266, u1_struct_0(A_265)) | ~l1_orders_2(A_265))), inference(resolution, [status(thm)], [c_815, c_2])).
% 3.47/1.62  tff(c_858, plain, (~v1_xboole_0(u1_orders_2('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_44, c_856])).
% 3.47/1.62  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_50, c_752, c_858])).
% 3.47/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.62  
% 3.47/1.62  Inference rules
% 3.47/1.62  ----------------------
% 3.47/1.62  #Ref     : 0
% 3.47/1.62  #Sup     : 176
% 3.47/1.62  #Fact    : 0
% 3.47/1.62  #Define  : 0
% 3.47/1.62  #Split   : 3
% 3.47/1.62  #Chain   : 0
% 3.47/1.62  #Close   : 0
% 3.47/1.62  
% 3.47/1.62  Ordering : KBO
% 3.47/1.62  
% 3.47/1.62  Simplification rules
% 3.47/1.62  ----------------------
% 3.47/1.62  #Subsume      : 26
% 3.47/1.62  #Demod        : 29
% 3.47/1.62  #Tautology    : 34
% 3.47/1.62  #SimpNegUnit  : 2
% 3.47/1.62  #BackRed      : 0
% 3.47/1.62  
% 3.47/1.62  #Partial instantiations: 0
% 3.47/1.62  #Strategies tried      : 1
% 3.47/1.62  
% 3.47/1.62  Timing (in seconds)
% 3.47/1.62  ----------------------
% 3.47/1.62  Preprocessing        : 0.33
% 3.47/1.62  Parsing              : 0.18
% 3.47/1.62  CNF conversion       : 0.03
% 3.47/1.62  Main loop            : 0.53
% 3.47/1.62  Inferencing          : 0.21
% 3.47/1.62  Reduction            : 0.12
% 3.47/1.62  Demodulation         : 0.08
% 3.47/1.62  BG Simplification    : 0.02
% 3.47/1.62  Subsumption          : 0.13
% 3.47/1.62  Abstraction          : 0.02
% 3.47/1.62  MUC search           : 0.00
% 3.47/1.62  Cooper               : 0.00
% 3.47/1.62  Total                : 0.89
% 3.47/1.62  Index Insertion      : 0.00
% 3.47/1.62  Index Deletion       : 0.00
% 3.47/1.62  Index Matching       : 0.00
% 3.47/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
