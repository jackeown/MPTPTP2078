%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:20 EST 2020

% Result     : Theorem 6.08s
% Output     : CNFRefutation 6.44s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 206 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  207 ( 805 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_2)).

tff(c_38,plain,(
    ~ r1_orders_2('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    ! [A_46] :
      ( m1_subset_1(u1_orders_2(A_46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_46),u1_struct_0(A_46))))
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_191,plain,(
    ! [B_129,C_130,A_131] :
      ( r2_hidden(k4_tarski(B_129,C_130),u1_orders_2(A_131))
      | ~ r1_orders_2(A_131,B_129,C_130)
      | ~ m1_subset_1(C_130,u1_struct_0(A_131))
      | ~ m1_subset_1(B_129,u1_struct_0(A_131))
      | ~ l1_orders_2(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_351,plain,(
    ! [B_181,C_182,A_183,A_184] :
      ( r2_hidden(k4_tarski(B_181,C_182),A_183)
      | ~ m1_subset_1(u1_orders_2(A_184),k1_zfmisc_1(A_183))
      | ~ r1_orders_2(A_184,B_181,C_182)
      | ~ m1_subset_1(C_182,u1_struct_0(A_184))
      | ~ m1_subset_1(B_181,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184) ) ),
    inference(resolution,[status(thm)],[c_191,c_8])).

tff(c_409,plain,(
    ! [B_227,C_228,A_229] :
      ( r2_hidden(k4_tarski(B_227,C_228),k2_zfmisc_1(u1_struct_0(A_229),u1_struct_0(A_229)))
      | ~ r1_orders_2(A_229,B_227,C_228)
      | ~ m1_subset_1(C_228,u1_struct_0(A_229))
      | ~ m1_subset_1(B_227,u1_struct_0(A_229))
      | ~ l1_orders_2(A_229) ) ),
    inference(resolution,[status(thm)],[c_36,c_351])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_434,plain,(
    ! [B_232,A_233,C_234] :
      ( r2_hidden(B_232,u1_struct_0(A_233))
      | ~ r1_orders_2(A_233,B_232,C_234)
      | ~ m1_subset_1(C_234,u1_struct_0(A_233))
      | ~ m1_subset_1(B_232,u1_struct_0(A_233))
      | ~ l1_orders_2(A_233) ) ),
    inference(resolution,[status(thm)],[c_409,c_6])).

tff(c_438,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_434])).

tff(c_444,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_438])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [A_81] :
      ( m1_subset_1(u1_orders_2(A_81),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81),u1_struct_0(A_81))))
      | ~ l1_orders_2(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [B_11,A_9] :
      ( v1_relat_1(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,(
    ! [A_81] :
      ( v1_relat_1(u1_orders_2(A_81))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_81),u1_struct_0(A_81)))
      | ~ l1_orders_2(A_81) ) ),
    inference(resolution,[status(thm)],[c_76,c_10])).

tff(c_82,plain,(
    ! [A_81] :
      ( v1_relat_1(u1_orders_2(A_81))
      | ~ l1_orders_2(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_52,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    r1_orders_2('#skF_4','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_30,plain,(
    ! [A_38] :
      ( r8_relat_2(u1_orders_2(A_38),u1_struct_0(A_38))
      | ~ v4_orders_2(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_440,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_434])).

tff(c_447,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_440])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_456,plain,(
    ! [C_237,A_238,B_239] :
      ( r2_hidden(C_237,u1_struct_0(A_238))
      | ~ r1_orders_2(A_238,B_239,C_237)
      | ~ m1_subset_1(C_237,u1_struct_0(A_238))
      | ~ m1_subset_1(B_239,u1_struct_0(A_238))
      | ~ l1_orders_2(A_238) ) ),
    inference(resolution,[status(thm)],[c_409,c_4])).

tff(c_462,plain,
    ( r2_hidden('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_456])).

tff(c_469,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_462])).

tff(c_34,plain,(
    ! [B_43,C_45,A_39] :
      ( r2_hidden(k4_tarski(B_43,C_45),u1_orders_2(A_39))
      | ~ r1_orders_2(A_39,B_43,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_subset_1(B_43,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_228,plain,(
    ! [B_148,E_144,C_145,D_146,A_147] :
      ( r2_hidden(k4_tarski(C_145,E_144),A_147)
      | ~ r2_hidden(k4_tarski(D_146,E_144),A_147)
      | ~ r2_hidden(k4_tarski(C_145,D_146),A_147)
      | ~ r2_hidden(E_144,B_148)
      | ~ r2_hidden(D_146,B_148)
      | ~ r2_hidden(C_145,B_148)
      | ~ r8_relat_2(A_147,B_148)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1147,plain,(
    ! [C_386,B_383,C_385,A_382,B_384] :
      ( r2_hidden(k4_tarski(C_386,C_385),u1_orders_2(A_382))
      | ~ r2_hidden(k4_tarski(C_386,B_383),u1_orders_2(A_382))
      | ~ r2_hidden(C_385,B_384)
      | ~ r2_hidden(B_383,B_384)
      | ~ r2_hidden(C_386,B_384)
      | ~ r8_relat_2(u1_orders_2(A_382),B_384)
      | ~ v1_relat_1(u1_orders_2(A_382))
      | ~ r1_orders_2(A_382,B_383,C_385)
      | ~ m1_subset_1(C_385,u1_struct_0(A_382))
      | ~ m1_subset_1(B_383,u1_struct_0(A_382))
      | ~ l1_orders_2(A_382) ) ),
    inference(resolution,[status(thm)],[c_34,c_228])).

tff(c_1858,plain,(
    ! [A_491,C_494,B_493,C_492,B_495] :
      ( r2_hidden(k4_tarski(B_493,C_492),u1_orders_2(A_491))
      | ~ r2_hidden(C_492,B_495)
      | ~ r2_hidden(C_494,B_495)
      | ~ r2_hidden(B_493,B_495)
      | ~ r8_relat_2(u1_orders_2(A_491),B_495)
      | ~ v1_relat_1(u1_orders_2(A_491))
      | ~ r1_orders_2(A_491,C_494,C_492)
      | ~ m1_subset_1(C_492,u1_struct_0(A_491))
      | ~ r1_orders_2(A_491,B_493,C_494)
      | ~ m1_subset_1(C_494,u1_struct_0(A_491))
      | ~ m1_subset_1(B_493,u1_struct_0(A_491))
      | ~ l1_orders_2(A_491) ) ),
    inference(resolution,[status(thm)],[c_34,c_1147])).

tff(c_2018,plain,(
    ! [B_506,A_507,C_508] :
      ( r2_hidden(k4_tarski(B_506,'#skF_7'),u1_orders_2(A_507))
      | ~ r2_hidden(C_508,u1_struct_0('#skF_4'))
      | ~ r2_hidden(B_506,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(u1_orders_2(A_507),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2(A_507))
      | ~ r1_orders_2(A_507,C_508,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_507))
      | ~ r1_orders_2(A_507,B_506,C_508)
      | ~ m1_subset_1(C_508,u1_struct_0(A_507))
      | ~ m1_subset_1(B_506,u1_struct_0(A_507))
      | ~ l1_orders_2(A_507) ) ),
    inference(resolution,[status(thm)],[c_469,c_1858])).

tff(c_2467,plain,(
    ! [B_548,A_549] :
      ( r2_hidden(k4_tarski(B_548,'#skF_7'),u1_orders_2(A_549))
      | ~ r2_hidden(B_548,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(u1_orders_2(A_549),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2(A_549))
      | ~ r1_orders_2(A_549,'#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_549))
      | ~ r1_orders_2(A_549,B_548,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_549))
      | ~ m1_subset_1(B_548,u1_struct_0(A_549))
      | ~ l1_orders_2(A_549) ) ),
    inference(resolution,[status(thm)],[c_447,c_2018])).

tff(c_2470,plain,(
    ! [B_548] :
      ( r2_hidden(k4_tarski(B_548,'#skF_7'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(B_548,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_4','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_548,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_548,u1_struct_0('#skF_4'))
      | ~ v4_orders_2('#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_2467])).

tff(c_2473,plain,(
    ! [B_548] :
      ( r2_hidden(k4_tarski(B_548,'#skF_7'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(B_548,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_548,'#skF_6')
      | ~ m1_subset_1(B_548,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_46,c_44,c_40,c_2470])).

tff(c_2474,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2473])).

tff(c_2477,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_2474])).

tff(c_2481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2477])).

tff(c_2484,plain,(
    ! [B_550] :
      ( r2_hidden(k4_tarski(B_550,'#skF_7'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(B_550,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_550,'#skF_6')
      | ~ m1_subset_1(B_550,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_2473])).

tff(c_32,plain,(
    ! [A_39,B_43,C_45] :
      ( r1_orders_2(A_39,B_43,C_45)
      | ~ r2_hidden(k4_tarski(B_43,C_45),u1_orders_2(A_39))
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_subset_1(B_43,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2499,plain,(
    ! [B_550] :
      ( r1_orders_2('#skF_4',B_550,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden(B_550,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_550,'#skF_6')
      | ~ m1_subset_1(B_550,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2484,c_32])).

tff(c_2516,plain,(
    ! [B_551] :
      ( r1_orders_2('#skF_4',B_551,'#skF_7')
      | ~ r2_hidden(B_551,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_551,'#skF_6')
      | ~ m1_subset_1(B_551,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_2499])).

tff(c_2593,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_7')
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_444,c_2516])).

tff(c_2689,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_2593])).

tff(c_2691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.08/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.20  
% 6.08/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.20  %$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 6.08/2.20  
% 6.08/2.20  %Foreground sorts:
% 6.08/2.20  
% 6.08/2.20  
% 6.08/2.20  %Background operators:
% 6.08/2.20  
% 6.08/2.20  
% 6.08/2.20  %Foreground operators:
% 6.08/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.08/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.08/2.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.08/2.20  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.08/2.20  tff('#skF_7', type, '#skF_7': $i).
% 6.08/2.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.08/2.20  tff('#skF_5', type, '#skF_5': $i).
% 6.08/2.20  tff('#skF_6', type, '#skF_6': $i).
% 6.08/2.20  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.08/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.08/2.20  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.08/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.08/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.08/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.08/2.20  tff('#skF_4', type, '#skF_4': $i).
% 6.08/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.08/2.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.08/2.20  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 6.08/2.20  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 6.08/2.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.08/2.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.08/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.08/2.20  
% 6.44/2.22  tff(f_107, negated_conjecture, ~(![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_orders_2)).
% 6.44/2.22  tff(f_87, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 6.44/2.22  tff(f_83, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 6.44/2.22  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.44/2.22  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 6.44/2.22  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.44/2.22  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.44/2.22  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (v4_orders_2(A) <=> r8_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_2)).
% 6.44/2.22  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (r8_relat_2(A, B) <=> (![C, D, E]: (((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(E, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, E), A)) => r2_hidden(k4_tarski(C, E), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_2)).
% 6.44/2.22  tff(c_38, plain, (~r1_orders_2('#skF_4', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.44/2.22  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.44/2.22  tff(c_42, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.44/2.22  tff(c_50, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.44/2.22  tff(c_46, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.44/2.22  tff(c_36, plain, (![A_46]: (m1_subset_1(u1_orders_2(A_46), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_46), u1_struct_0(A_46)))) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.44/2.22  tff(c_191, plain, (![B_129, C_130, A_131]: (r2_hidden(k4_tarski(B_129, C_130), u1_orders_2(A_131)) | ~r1_orders_2(A_131, B_129, C_130) | ~m1_subset_1(C_130, u1_struct_0(A_131)) | ~m1_subset_1(B_129, u1_struct_0(A_131)) | ~l1_orders_2(A_131))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.44/2.22  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.44/2.22  tff(c_351, plain, (![B_181, C_182, A_183, A_184]: (r2_hidden(k4_tarski(B_181, C_182), A_183) | ~m1_subset_1(u1_orders_2(A_184), k1_zfmisc_1(A_183)) | ~r1_orders_2(A_184, B_181, C_182) | ~m1_subset_1(C_182, u1_struct_0(A_184)) | ~m1_subset_1(B_181, u1_struct_0(A_184)) | ~l1_orders_2(A_184))), inference(resolution, [status(thm)], [c_191, c_8])).
% 6.44/2.22  tff(c_409, plain, (![B_227, C_228, A_229]: (r2_hidden(k4_tarski(B_227, C_228), k2_zfmisc_1(u1_struct_0(A_229), u1_struct_0(A_229))) | ~r1_orders_2(A_229, B_227, C_228) | ~m1_subset_1(C_228, u1_struct_0(A_229)) | ~m1_subset_1(B_227, u1_struct_0(A_229)) | ~l1_orders_2(A_229))), inference(resolution, [status(thm)], [c_36, c_351])).
% 6.44/2.22  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.44/2.22  tff(c_434, plain, (![B_232, A_233, C_234]: (r2_hidden(B_232, u1_struct_0(A_233)) | ~r1_orders_2(A_233, B_232, C_234) | ~m1_subset_1(C_234, u1_struct_0(A_233)) | ~m1_subset_1(B_232, u1_struct_0(A_233)) | ~l1_orders_2(A_233))), inference(resolution, [status(thm)], [c_409, c_6])).
% 6.44/2.22  tff(c_438, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_42, c_434])).
% 6.44/2.22  tff(c_444, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_438])).
% 6.44/2.22  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.44/2.22  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.44/2.22  tff(c_76, plain, (![A_81]: (m1_subset_1(u1_orders_2(A_81), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81), u1_struct_0(A_81)))) | ~l1_orders_2(A_81))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.44/2.22  tff(c_10, plain, (![B_11, A_9]: (v1_relat_1(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.44/2.22  tff(c_79, plain, (![A_81]: (v1_relat_1(u1_orders_2(A_81)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_81), u1_struct_0(A_81))) | ~l1_orders_2(A_81))), inference(resolution, [status(thm)], [c_76, c_10])).
% 6.44/2.22  tff(c_82, plain, (![A_81]: (v1_relat_1(u1_orders_2(A_81)) | ~l1_orders_2(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_79])).
% 6.44/2.22  tff(c_52, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.44/2.22  tff(c_40, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.44/2.22  tff(c_30, plain, (![A_38]: (r8_relat_2(u1_orders_2(A_38), u1_struct_0(A_38)) | ~v4_orders_2(A_38) | ~l1_orders_2(A_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.44/2.22  tff(c_440, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_40, c_434])).
% 6.44/2.22  tff(c_447, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44, c_440])).
% 6.44/2.22  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.44/2.22  tff(c_456, plain, (![C_237, A_238, B_239]: (r2_hidden(C_237, u1_struct_0(A_238)) | ~r1_orders_2(A_238, B_239, C_237) | ~m1_subset_1(C_237, u1_struct_0(A_238)) | ~m1_subset_1(B_239, u1_struct_0(A_238)) | ~l1_orders_2(A_238))), inference(resolution, [status(thm)], [c_409, c_4])).
% 6.44/2.22  tff(c_462, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_40, c_456])).
% 6.44/2.22  tff(c_469, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44, c_462])).
% 6.44/2.22  tff(c_34, plain, (![B_43, C_45, A_39]: (r2_hidden(k4_tarski(B_43, C_45), u1_orders_2(A_39)) | ~r1_orders_2(A_39, B_43, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_subset_1(B_43, u1_struct_0(A_39)) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.44/2.22  tff(c_228, plain, (![B_148, E_144, C_145, D_146, A_147]: (r2_hidden(k4_tarski(C_145, E_144), A_147) | ~r2_hidden(k4_tarski(D_146, E_144), A_147) | ~r2_hidden(k4_tarski(C_145, D_146), A_147) | ~r2_hidden(E_144, B_148) | ~r2_hidden(D_146, B_148) | ~r2_hidden(C_145, B_148) | ~r8_relat_2(A_147, B_148) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.44/2.22  tff(c_1147, plain, (![C_386, B_383, C_385, A_382, B_384]: (r2_hidden(k4_tarski(C_386, C_385), u1_orders_2(A_382)) | ~r2_hidden(k4_tarski(C_386, B_383), u1_orders_2(A_382)) | ~r2_hidden(C_385, B_384) | ~r2_hidden(B_383, B_384) | ~r2_hidden(C_386, B_384) | ~r8_relat_2(u1_orders_2(A_382), B_384) | ~v1_relat_1(u1_orders_2(A_382)) | ~r1_orders_2(A_382, B_383, C_385) | ~m1_subset_1(C_385, u1_struct_0(A_382)) | ~m1_subset_1(B_383, u1_struct_0(A_382)) | ~l1_orders_2(A_382))), inference(resolution, [status(thm)], [c_34, c_228])).
% 6.44/2.22  tff(c_1858, plain, (![A_491, C_494, B_493, C_492, B_495]: (r2_hidden(k4_tarski(B_493, C_492), u1_orders_2(A_491)) | ~r2_hidden(C_492, B_495) | ~r2_hidden(C_494, B_495) | ~r2_hidden(B_493, B_495) | ~r8_relat_2(u1_orders_2(A_491), B_495) | ~v1_relat_1(u1_orders_2(A_491)) | ~r1_orders_2(A_491, C_494, C_492) | ~m1_subset_1(C_492, u1_struct_0(A_491)) | ~r1_orders_2(A_491, B_493, C_494) | ~m1_subset_1(C_494, u1_struct_0(A_491)) | ~m1_subset_1(B_493, u1_struct_0(A_491)) | ~l1_orders_2(A_491))), inference(resolution, [status(thm)], [c_34, c_1147])).
% 6.44/2.22  tff(c_2018, plain, (![B_506, A_507, C_508]: (r2_hidden(k4_tarski(B_506, '#skF_7'), u1_orders_2(A_507)) | ~r2_hidden(C_508, u1_struct_0('#skF_4')) | ~r2_hidden(B_506, u1_struct_0('#skF_4')) | ~r8_relat_2(u1_orders_2(A_507), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_orders_2(A_507)) | ~r1_orders_2(A_507, C_508, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0(A_507)) | ~r1_orders_2(A_507, B_506, C_508) | ~m1_subset_1(C_508, u1_struct_0(A_507)) | ~m1_subset_1(B_506, u1_struct_0(A_507)) | ~l1_orders_2(A_507))), inference(resolution, [status(thm)], [c_469, c_1858])).
% 6.44/2.22  tff(c_2467, plain, (![B_548, A_549]: (r2_hidden(k4_tarski(B_548, '#skF_7'), u1_orders_2(A_549)) | ~r2_hidden(B_548, u1_struct_0('#skF_4')) | ~r8_relat_2(u1_orders_2(A_549), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_orders_2(A_549)) | ~r1_orders_2(A_549, '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0(A_549)) | ~r1_orders_2(A_549, B_548, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(A_549)) | ~m1_subset_1(B_548, u1_struct_0(A_549)) | ~l1_orders_2(A_549))), inference(resolution, [status(thm)], [c_447, c_2018])).
% 6.44/2.22  tff(c_2470, plain, (![B_548]: (r2_hidden(k4_tarski(B_548, '#skF_7'), u1_orders_2('#skF_4')) | ~r2_hidden(B_548, u1_struct_0('#skF_4')) | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~r1_orders_2('#skF_4', B_548, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(B_548, u1_struct_0('#skF_4')) | ~v4_orders_2('#skF_4') | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_2467])).
% 6.44/2.22  tff(c_2473, plain, (![B_548]: (r2_hidden(k4_tarski(B_548, '#skF_7'), u1_orders_2('#skF_4')) | ~r2_hidden(B_548, u1_struct_0('#skF_4')) | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', B_548, '#skF_6') | ~m1_subset_1(B_548, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_46, c_44, c_40, c_2470])).
% 6.44/2.22  tff(c_2474, plain, (~v1_relat_1(u1_orders_2('#skF_4'))), inference(splitLeft, [status(thm)], [c_2473])).
% 6.44/2.22  tff(c_2477, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_82, c_2474])).
% 6.44/2.22  tff(c_2481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_2477])).
% 6.44/2.22  tff(c_2484, plain, (![B_550]: (r2_hidden(k4_tarski(B_550, '#skF_7'), u1_orders_2('#skF_4')) | ~r2_hidden(B_550, u1_struct_0('#skF_4')) | ~r1_orders_2('#skF_4', B_550, '#skF_6') | ~m1_subset_1(B_550, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2473])).
% 6.44/2.22  tff(c_32, plain, (![A_39, B_43, C_45]: (r1_orders_2(A_39, B_43, C_45) | ~r2_hidden(k4_tarski(B_43, C_45), u1_orders_2(A_39)) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_subset_1(B_43, u1_struct_0(A_39)) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.44/2.22  tff(c_2499, plain, (![B_550]: (r1_orders_2('#skF_4', B_550, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden(B_550, u1_struct_0('#skF_4')) | ~r1_orders_2('#skF_4', B_550, '#skF_6') | ~m1_subset_1(B_550, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2484, c_32])).
% 6.44/2.22  tff(c_2516, plain, (![B_551]: (r1_orders_2('#skF_4', B_551, '#skF_7') | ~r2_hidden(B_551, u1_struct_0('#skF_4')) | ~r1_orders_2('#skF_4', B_551, '#skF_6') | ~m1_subset_1(B_551, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_2499])).
% 6.44/2.22  tff(c_2593, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_7') | ~r1_orders_2('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_444, c_2516])).
% 6.44/2.22  tff(c_2689, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_2593])).
% 6.44/2.22  tff(c_2691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_2689])).
% 6.44/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.44/2.22  
% 6.44/2.22  Inference rules
% 6.44/2.22  ----------------------
% 6.44/2.22  #Ref     : 0
% 6.44/2.22  #Sup     : 629
% 6.44/2.22  #Fact    : 0
% 6.44/2.22  #Define  : 0
% 6.44/2.22  #Split   : 1
% 6.44/2.22  #Chain   : 0
% 6.44/2.22  #Close   : 0
% 6.44/2.22  
% 6.44/2.22  Ordering : KBO
% 6.44/2.22  
% 6.44/2.22  Simplification rules
% 6.44/2.22  ----------------------
% 6.44/2.22  #Subsume      : 40
% 6.44/2.22  #Demod        : 313
% 6.44/2.22  #Tautology    : 103
% 6.44/2.22  #SimpNegUnit  : 1
% 6.44/2.22  #BackRed      : 0
% 6.44/2.22  
% 6.44/2.22  #Partial instantiations: 0
% 6.44/2.22  #Strategies tried      : 1
% 6.44/2.22  
% 6.44/2.22  Timing (in seconds)
% 6.44/2.22  ----------------------
% 6.44/2.22  Preprocessing        : 0.30
% 6.44/2.22  Parsing              : 0.17
% 6.44/2.22  CNF conversion       : 0.02
% 6.44/2.22  Main loop            : 1.14
% 6.44/2.22  Inferencing          : 0.36
% 6.44/2.22  Reduction            : 0.27
% 6.44/2.22  Demodulation         : 0.19
% 6.44/2.22  BG Simplification    : 0.04
% 6.44/2.22  Subsumption          : 0.39
% 6.44/2.22  Abstraction          : 0.05
% 6.44/2.22  MUC search           : 0.00
% 6.44/2.22  Cooper               : 0.00
% 6.44/2.22  Total                : 1.48
% 6.44/2.22  Index Insertion      : 0.00
% 6.44/2.22  Index Deletion       : 0.00
% 6.44/2.22  Index Matching       : 0.00
% 6.44/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
