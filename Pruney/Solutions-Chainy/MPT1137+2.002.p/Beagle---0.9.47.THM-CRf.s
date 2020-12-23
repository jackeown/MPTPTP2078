%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:19 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 100 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 317 expanded)
%              Number of equality atoms :   11 (  25 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_70,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_121,plain,(
    ! [A_69] :
      ( m1_subset_1(u1_orders_2(A_69),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_69),u1_struct_0(A_69))))
      | ~ l1_orders_2(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,(
    ! [A_69] :
      ( v1_relat_1(u1_orders_2(A_69))
      | ~ l1_orders_2(A_69) ) ),
    inference(resolution,[status(thm)],[c_121,c_12])).

tff(c_53,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_53])).

tff(c_66,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    ! [A_29] :
      ( r4_relat_2(u1_orders_2(A_29),u1_struct_0(A_29))
      | ~ v5_orders_2(A_29)
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [B_34,C_36,A_30] :
      ( r2_hidden(k4_tarski(B_34,C_36),u1_orders_2(A_30))
      | ~ r1_orders_2(A_30,B_34,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0(A_30))
      | ~ m1_subset_1(B_34,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_283,plain,(
    ! [D_105,C_106,A_107,B_108] :
      ( D_105 = C_106
      | ~ r2_hidden(k4_tarski(D_105,C_106),A_107)
      | ~ r2_hidden(k4_tarski(C_106,D_105),A_107)
      | ~ r2_hidden(D_105,B_108)
      | ~ r2_hidden(C_106,B_108)
      | ~ r4_relat_2(A_107,B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_480,plain,(
    ! [C_177,B_178,A_179,B_180] :
      ( C_177 = B_178
      | ~ r2_hidden(k4_tarski(C_177,B_178),u1_orders_2(A_179))
      | ~ r2_hidden(B_178,B_180)
      | ~ r2_hidden(C_177,B_180)
      | ~ r4_relat_2(u1_orders_2(A_179),B_180)
      | ~ v1_relat_1(u1_orders_2(A_179))
      | ~ r1_orders_2(A_179,B_178,C_177)
      | ~ m1_subset_1(C_177,u1_struct_0(A_179))
      | ~ m1_subset_1(B_178,u1_struct_0(A_179))
      | ~ l1_orders_2(A_179) ) ),
    inference(resolution,[status(thm)],[c_34,c_283])).

tff(c_496,plain,(
    ! [C_181,B_182,B_183,A_184] :
      ( C_181 = B_182
      | ~ r2_hidden(C_181,B_183)
      | ~ r2_hidden(B_182,B_183)
      | ~ r4_relat_2(u1_orders_2(A_184),B_183)
      | ~ v1_relat_1(u1_orders_2(A_184))
      | ~ r1_orders_2(A_184,C_181,B_182)
      | ~ r1_orders_2(A_184,B_182,C_181)
      | ~ m1_subset_1(C_181,u1_struct_0(A_184))
      | ~ m1_subset_1(B_182,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184) ) ),
    inference(resolution,[status(thm)],[c_34,c_480])).

tff(c_515,plain,(
    ! [B_186,B_185,A_187,A_188] :
      ( B_186 = B_185
      | ~ r2_hidden(B_186,A_187)
      | ~ r4_relat_2(u1_orders_2(A_188),A_187)
      | ~ v1_relat_1(u1_orders_2(A_188))
      | ~ r1_orders_2(A_188,B_185,B_186)
      | ~ r1_orders_2(A_188,B_186,B_185)
      | ~ m1_subset_1(B_185,u1_struct_0(A_188))
      | ~ m1_subset_1(B_186,u1_struct_0(A_188))
      | ~ l1_orders_2(A_188)
      | ~ m1_subset_1(B_185,A_187)
      | v1_xboole_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_6,c_496])).

tff(c_558,plain,(
    ! [B_198,B_197,A_199,A_200] :
      ( B_198 = B_197
      | ~ r4_relat_2(u1_orders_2(A_199),A_200)
      | ~ v1_relat_1(u1_orders_2(A_199))
      | ~ r1_orders_2(A_199,B_198,B_197)
      | ~ r1_orders_2(A_199,B_197,B_198)
      | ~ m1_subset_1(B_198,u1_struct_0(A_199))
      | ~ m1_subset_1(B_197,u1_struct_0(A_199))
      | ~ l1_orders_2(A_199)
      | ~ m1_subset_1(B_198,A_200)
      | ~ m1_subset_1(B_197,A_200)
      | v1_xboole_0(A_200) ) ),
    inference(resolution,[status(thm)],[c_6,c_515])).

tff(c_574,plain,(
    ! [B_202,B_201,A_203] :
      ( B_202 = B_201
      | ~ v1_relat_1(u1_orders_2(A_203))
      | ~ r1_orders_2(A_203,B_201,B_202)
      | ~ r1_orders_2(A_203,B_202,B_201)
      | ~ m1_subset_1(B_201,u1_struct_0(A_203))
      | ~ m1_subset_1(B_202,u1_struct_0(A_203))
      | v1_xboole_0(u1_struct_0(A_203))
      | ~ v5_orders_2(A_203)
      | ~ l1_orders_2(A_203) ) ),
    inference(resolution,[status(thm)],[c_30,c_558])).

tff(c_580,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_relat_1(u1_orders_2('#skF_3'))
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ v5_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_574])).

tff(c_587,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_relat_1(u1_orders_2('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_46,c_44,c_42,c_580])).

tff(c_588,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_38,c_587])).

tff(c_595,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_588])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_595])).

tff(c_601,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_664,plain,(
    ! [A_225] :
      ( m1_subset_1(u1_orders_2(A_225),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225),u1_struct_0(A_225))))
      | ~ l1_orders_2(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [C_11,B_9,A_8] :
      ( v1_xboole_0(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(B_9,A_8)))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_678,plain,(
    ! [A_227] :
      ( v1_xboole_0(u1_orders_2(A_227))
      | ~ v1_xboole_0(u1_struct_0(A_227))
      | ~ l1_orders_2(A_227) ) ),
    inference(resolution,[status(thm)],[c_664,c_14])).

tff(c_681,plain,
    ( v1_xboole_0(u1_orders_2('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_601,c_678])).

tff(c_684,plain,(
    v1_xboole_0(u1_orders_2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_681])).

tff(c_779,plain,(
    ! [B_249,C_250,A_251] :
      ( r2_hidden(k4_tarski(B_249,C_250),u1_orders_2(A_251))
      | ~ r1_orders_2(A_251,B_249,C_250)
      | ~ m1_subset_1(C_250,u1_struct_0(A_251))
      | ~ m1_subset_1(B_249,u1_struct_0(A_251))
      | ~ l1_orders_2(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_808,plain,(
    ! [A_255,B_256,C_257] :
      ( ~ v1_xboole_0(u1_orders_2(A_255))
      | ~ r1_orders_2(A_255,B_256,C_257)
      | ~ m1_subset_1(C_257,u1_struct_0(A_255))
      | ~ m1_subset_1(B_256,u1_struct_0(A_255))
      | ~ l1_orders_2(A_255) ) ),
    inference(resolution,[status(thm)],[c_779,c_2])).

tff(c_810,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_808])).

tff(c_816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_684,c_810])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.55  
% 3.33/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.55  %$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.33/1.55  
% 3.33/1.55  %Foreground sorts:
% 3.33/1.55  
% 3.33/1.55  
% 3.33/1.55  %Background operators:
% 3.33/1.55  
% 3.33/1.55  
% 3.33/1.55  %Foreground operators:
% 3.33/1.55  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 3.33/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.33/1.55  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.33/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.33/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.33/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.55  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.33/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.33/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.55  
% 3.33/1.57  tff(f_109, negated_conjecture, ~(![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 3.33/1.57  tff(f_92, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 3.33/1.57  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.33/1.57  tff(f_43, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.33/1.57  tff(f_76, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_orders_2)).
% 3.33/1.57  tff(f_88, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 3.33/1.57  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (r4_relat_2(A, B) <=> (![C, D]: ((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, C), A)) => (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_2)).
% 3.33/1.57  tff(f_54, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.33/1.57  tff(f_30, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 3.33/1.57  tff(c_48, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.33/1.57  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.33/1.57  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.33/1.57  tff(c_121, plain, (![A_69]: (m1_subset_1(u1_orders_2(A_69), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_69), u1_struct_0(A_69)))) | ~l1_orders_2(A_69))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.33/1.57  tff(c_12, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.33/1.57  tff(c_132, plain, (![A_69]: (v1_relat_1(u1_orders_2(A_69)) | ~l1_orders_2(A_69))), inference(resolution, [status(thm)], [c_121, c_12])).
% 3.33/1.57  tff(c_53, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.33/1.57  tff(c_64, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_53])).
% 3.33/1.57  tff(c_66, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 3.33/1.57  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.33/1.57  tff(c_50, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.33/1.57  tff(c_42, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.33/1.57  tff(c_40, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.33/1.57  tff(c_30, plain, (![A_29]: (r4_relat_2(u1_orders_2(A_29), u1_struct_0(A_29)) | ~v5_orders_2(A_29) | ~l1_orders_2(A_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.33/1.57  tff(c_6, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.33/1.57  tff(c_34, plain, (![B_34, C_36, A_30]: (r2_hidden(k4_tarski(B_34, C_36), u1_orders_2(A_30)) | ~r1_orders_2(A_30, B_34, C_36) | ~m1_subset_1(C_36, u1_struct_0(A_30)) | ~m1_subset_1(B_34, u1_struct_0(A_30)) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.33/1.57  tff(c_283, plain, (![D_105, C_106, A_107, B_108]: (D_105=C_106 | ~r2_hidden(k4_tarski(D_105, C_106), A_107) | ~r2_hidden(k4_tarski(C_106, D_105), A_107) | ~r2_hidden(D_105, B_108) | ~r2_hidden(C_106, B_108) | ~r4_relat_2(A_107, B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.33/1.57  tff(c_480, plain, (![C_177, B_178, A_179, B_180]: (C_177=B_178 | ~r2_hidden(k4_tarski(C_177, B_178), u1_orders_2(A_179)) | ~r2_hidden(B_178, B_180) | ~r2_hidden(C_177, B_180) | ~r4_relat_2(u1_orders_2(A_179), B_180) | ~v1_relat_1(u1_orders_2(A_179)) | ~r1_orders_2(A_179, B_178, C_177) | ~m1_subset_1(C_177, u1_struct_0(A_179)) | ~m1_subset_1(B_178, u1_struct_0(A_179)) | ~l1_orders_2(A_179))), inference(resolution, [status(thm)], [c_34, c_283])).
% 3.33/1.57  tff(c_496, plain, (![C_181, B_182, B_183, A_184]: (C_181=B_182 | ~r2_hidden(C_181, B_183) | ~r2_hidden(B_182, B_183) | ~r4_relat_2(u1_orders_2(A_184), B_183) | ~v1_relat_1(u1_orders_2(A_184)) | ~r1_orders_2(A_184, C_181, B_182) | ~r1_orders_2(A_184, B_182, C_181) | ~m1_subset_1(C_181, u1_struct_0(A_184)) | ~m1_subset_1(B_182, u1_struct_0(A_184)) | ~l1_orders_2(A_184))), inference(resolution, [status(thm)], [c_34, c_480])).
% 3.33/1.57  tff(c_515, plain, (![B_186, B_185, A_187, A_188]: (B_186=B_185 | ~r2_hidden(B_186, A_187) | ~r4_relat_2(u1_orders_2(A_188), A_187) | ~v1_relat_1(u1_orders_2(A_188)) | ~r1_orders_2(A_188, B_185, B_186) | ~r1_orders_2(A_188, B_186, B_185) | ~m1_subset_1(B_185, u1_struct_0(A_188)) | ~m1_subset_1(B_186, u1_struct_0(A_188)) | ~l1_orders_2(A_188) | ~m1_subset_1(B_185, A_187) | v1_xboole_0(A_187))), inference(resolution, [status(thm)], [c_6, c_496])).
% 3.33/1.57  tff(c_558, plain, (![B_198, B_197, A_199, A_200]: (B_198=B_197 | ~r4_relat_2(u1_orders_2(A_199), A_200) | ~v1_relat_1(u1_orders_2(A_199)) | ~r1_orders_2(A_199, B_198, B_197) | ~r1_orders_2(A_199, B_197, B_198) | ~m1_subset_1(B_198, u1_struct_0(A_199)) | ~m1_subset_1(B_197, u1_struct_0(A_199)) | ~l1_orders_2(A_199) | ~m1_subset_1(B_198, A_200) | ~m1_subset_1(B_197, A_200) | v1_xboole_0(A_200))), inference(resolution, [status(thm)], [c_6, c_515])).
% 3.33/1.57  tff(c_574, plain, (![B_202, B_201, A_203]: (B_202=B_201 | ~v1_relat_1(u1_orders_2(A_203)) | ~r1_orders_2(A_203, B_201, B_202) | ~r1_orders_2(A_203, B_202, B_201) | ~m1_subset_1(B_201, u1_struct_0(A_203)) | ~m1_subset_1(B_202, u1_struct_0(A_203)) | v1_xboole_0(u1_struct_0(A_203)) | ~v5_orders_2(A_203) | ~l1_orders_2(A_203))), inference(resolution, [status(thm)], [c_30, c_558])).
% 3.33/1.57  tff(c_580, plain, ('#skF_5'='#skF_4' | ~v1_relat_1(u1_orders_2('#skF_3')) | ~r1_orders_2('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~v5_orders_2('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_40, c_574])).
% 3.33/1.57  tff(c_587, plain, ('#skF_5'='#skF_4' | ~v1_relat_1(u1_orders_2('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_46, c_44, c_42, c_580])).
% 3.33/1.57  tff(c_588, plain, (~v1_relat_1(u1_orders_2('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_38, c_587])).
% 3.33/1.57  tff(c_595, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_132, c_588])).
% 3.33/1.57  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_595])).
% 3.33/1.57  tff(c_601, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 3.33/1.57  tff(c_664, plain, (![A_225]: (m1_subset_1(u1_orders_2(A_225), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225), u1_struct_0(A_225)))) | ~l1_orders_2(A_225))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.33/1.57  tff(c_14, plain, (![C_11, B_9, A_8]: (v1_xboole_0(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(B_9, A_8))) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.57  tff(c_678, plain, (![A_227]: (v1_xboole_0(u1_orders_2(A_227)) | ~v1_xboole_0(u1_struct_0(A_227)) | ~l1_orders_2(A_227))), inference(resolution, [status(thm)], [c_664, c_14])).
% 3.33/1.57  tff(c_681, plain, (v1_xboole_0(u1_orders_2('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_601, c_678])).
% 3.33/1.57  tff(c_684, plain, (v1_xboole_0(u1_orders_2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_681])).
% 3.33/1.57  tff(c_779, plain, (![B_249, C_250, A_251]: (r2_hidden(k4_tarski(B_249, C_250), u1_orders_2(A_251)) | ~r1_orders_2(A_251, B_249, C_250) | ~m1_subset_1(C_250, u1_struct_0(A_251)) | ~m1_subset_1(B_249, u1_struct_0(A_251)) | ~l1_orders_2(A_251))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.33/1.57  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.33/1.57  tff(c_808, plain, (![A_255, B_256, C_257]: (~v1_xboole_0(u1_orders_2(A_255)) | ~r1_orders_2(A_255, B_256, C_257) | ~m1_subset_1(C_257, u1_struct_0(A_255)) | ~m1_subset_1(B_256, u1_struct_0(A_255)) | ~l1_orders_2(A_255))), inference(resolution, [status(thm)], [c_779, c_2])).
% 3.33/1.57  tff(c_810, plain, (~v1_xboole_0(u1_orders_2('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_40, c_808])).
% 3.33/1.57  tff(c_816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_684, c_810])).
% 3.33/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.57  
% 3.33/1.57  Inference rules
% 3.33/1.57  ----------------------
% 3.33/1.57  #Ref     : 0
% 3.33/1.57  #Sup     : 161
% 3.33/1.57  #Fact    : 0
% 3.33/1.57  #Define  : 0
% 3.33/1.57  #Split   : 3
% 3.33/1.57  #Chain   : 0
% 3.33/1.57  #Close   : 0
% 3.33/1.57  
% 3.33/1.57  Ordering : KBO
% 3.33/1.57  
% 3.33/1.57  Simplification rules
% 3.33/1.57  ----------------------
% 3.33/1.57  #Subsume      : 30
% 3.33/1.57  #Demod        : 27
% 3.33/1.57  #Tautology    : 28
% 3.33/1.57  #SimpNegUnit  : 18
% 3.33/1.57  #BackRed      : 0
% 3.33/1.57  
% 3.33/1.57  #Partial instantiations: 0
% 3.33/1.57  #Strategies tried      : 1
% 3.33/1.57  
% 3.33/1.57  Timing (in seconds)
% 3.33/1.57  ----------------------
% 3.33/1.57  Preprocessing        : 0.31
% 3.33/1.57  Parsing              : 0.17
% 3.33/1.57  CNF conversion       : 0.02
% 3.33/1.57  Main loop            : 0.45
% 3.33/1.57  Inferencing          : 0.18
% 3.33/1.57  Reduction            : 0.10
% 3.33/1.57  Demodulation         : 0.06
% 3.33/1.57  BG Simplification    : 0.02
% 3.33/1.57  Subsumption          : 0.12
% 3.33/1.57  Abstraction          : 0.02
% 3.33/1.57  MUC search           : 0.00
% 3.33/1.57  Cooper               : 0.00
% 3.33/1.57  Total                : 0.79
% 3.33/1.57  Index Insertion      : 0.00
% 3.33/1.57  Index Deletion       : 0.00
% 3.33/1.57  Index Matching       : 0.00
% 3.33/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
