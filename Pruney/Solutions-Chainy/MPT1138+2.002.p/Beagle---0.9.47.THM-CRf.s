%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:20 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 203 expanded)
%              Number of leaves         :   30 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  200 ( 798 expanded)
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

tff(f_102,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_78,axiom,(
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

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

tff(f_60,axiom,(
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

tff(c_36,plain,(
    ~ r1_orders_2('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    ! [A_44] :
      ( m1_subset_1(u1_orders_2(A_44),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_44),u1_struct_0(A_44))))
      | ~ l1_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_133,plain,(
    ! [B_96,C_97,A_98] :
      ( r2_hidden(k4_tarski(B_96,C_97),u1_orders_2(A_98))
      | ~ r1_orders_2(A_98,B_96,C_97)
      | ~ m1_subset_1(C_97,u1_struct_0(A_98))
      | ~ m1_subset_1(B_96,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_303,plain,(
    ! [B_176,C_177,A_178,A_179] :
      ( r2_hidden(k4_tarski(B_176,C_177),A_178)
      | ~ m1_subset_1(u1_orders_2(A_179),k1_zfmisc_1(A_178))
      | ~ r1_orders_2(A_179,B_176,C_177)
      | ~ m1_subset_1(C_177,u1_struct_0(A_179))
      | ~ m1_subset_1(B_176,u1_struct_0(A_179))
      | ~ l1_orders_2(A_179) ) ),
    inference(resolution,[status(thm)],[c_133,c_8])).

tff(c_340,plain,(
    ! [B_208,C_209,A_210] :
      ( r2_hidden(k4_tarski(B_208,C_209),k2_zfmisc_1(u1_struct_0(A_210),u1_struct_0(A_210)))
      | ~ r1_orders_2(A_210,B_208,C_209)
      | ~ m1_subset_1(C_209,u1_struct_0(A_210))
      | ~ m1_subset_1(B_208,u1_struct_0(A_210))
      | ~ l1_orders_2(A_210) ) ),
    inference(resolution,[status(thm)],[c_34,c_303])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_360,plain,(
    ! [B_211,A_212,C_213] :
      ( r2_hidden(B_211,u1_struct_0(A_212))
      | ~ r1_orders_2(A_212,B_211,C_213)
      | ~ m1_subset_1(C_213,u1_struct_0(A_212))
      | ~ m1_subset_1(B_211,u1_struct_0(A_212))
      | ~ l1_orders_2(A_212) ) ),
    inference(resolution,[status(thm)],[c_340,c_6])).

tff(c_362,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_360])).

tff(c_367,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_362])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_73,plain,(
    ! [A_78] :
      ( m1_subset_1(u1_orders_2(A_78),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78),u1_struct_0(A_78))))
      | ~ l1_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_77,plain,(
    ! [A_78] :
      ( v1_relat_1(u1_orders_2(A_78))
      | ~ l1_orders_2(A_78) ) ),
    inference(resolution,[status(thm)],[c_73,c_10])).

tff(c_50,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    r1_orders_2('#skF_4','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    ! [A_36] :
      ( r8_relat_2(u1_orders_2(A_36),u1_struct_0(A_36))
      | ~ v4_orders_2(A_36)
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_364,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_360])).

tff(c_370,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_364])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_379,plain,(
    ! [C_216,A_217,B_218] :
      ( r2_hidden(C_216,u1_struct_0(A_217))
      | ~ r1_orders_2(A_217,B_218,C_216)
      | ~ m1_subset_1(C_216,u1_struct_0(A_217))
      | ~ m1_subset_1(B_218,u1_struct_0(A_217))
      | ~ l1_orders_2(A_217) ) ),
    inference(resolution,[status(thm)],[c_340,c_4])).

tff(c_383,plain,
    ( r2_hidden('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_379])).

tff(c_389,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_383])).

tff(c_32,plain,(
    ! [B_41,C_43,A_37] :
      ( r2_hidden(k4_tarski(B_41,C_43),u1_orders_2(A_37))
      | ~ r1_orders_2(A_37,B_41,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_37))
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_201,plain,(
    ! [B_133,C_132,E_130,A_131,D_129] :
      ( r2_hidden(k4_tarski(C_132,E_130),A_131)
      | ~ r2_hidden(k4_tarski(D_129,E_130),A_131)
      | ~ r2_hidden(k4_tarski(C_132,D_129),A_131)
      | ~ r2_hidden(E_130,B_133)
      | ~ r2_hidden(D_129,B_133)
      | ~ r2_hidden(C_132,B_133)
      | ~ r8_relat_2(A_131,B_133)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1135,plain,(
    ! [B_386,C_383,A_384,C_385,B_387] :
      ( r2_hidden(k4_tarski(C_383,C_385),u1_orders_2(A_384))
      | ~ r2_hidden(k4_tarski(C_383,B_387),u1_orders_2(A_384))
      | ~ r2_hidden(C_385,B_386)
      | ~ r2_hidden(B_387,B_386)
      | ~ r2_hidden(C_383,B_386)
      | ~ r8_relat_2(u1_orders_2(A_384),B_386)
      | ~ v1_relat_1(u1_orders_2(A_384))
      | ~ r1_orders_2(A_384,B_387,C_385)
      | ~ m1_subset_1(C_385,u1_struct_0(A_384))
      | ~ m1_subset_1(B_387,u1_struct_0(A_384))
      | ~ l1_orders_2(A_384) ) ),
    inference(resolution,[status(thm)],[c_32,c_201])).

tff(c_1726,plain,(
    ! [B_508,C_506,A_505,B_507,C_504] :
      ( r2_hidden(k4_tarski(B_508,C_504),u1_orders_2(A_505))
      | ~ r2_hidden(C_504,B_507)
      | ~ r2_hidden(C_506,B_507)
      | ~ r2_hidden(B_508,B_507)
      | ~ r8_relat_2(u1_orders_2(A_505),B_507)
      | ~ v1_relat_1(u1_orders_2(A_505))
      | ~ r1_orders_2(A_505,C_506,C_504)
      | ~ m1_subset_1(C_504,u1_struct_0(A_505))
      | ~ r1_orders_2(A_505,B_508,C_506)
      | ~ m1_subset_1(C_506,u1_struct_0(A_505))
      | ~ m1_subset_1(B_508,u1_struct_0(A_505))
      | ~ l1_orders_2(A_505) ) ),
    inference(resolution,[status(thm)],[c_32,c_1135])).

tff(c_1899,plain,(
    ! [B_514,A_515,C_516] :
      ( r2_hidden(k4_tarski(B_514,'#skF_7'),u1_orders_2(A_515))
      | ~ r2_hidden(C_516,u1_struct_0('#skF_4'))
      | ~ r2_hidden(B_514,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(u1_orders_2(A_515),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2(A_515))
      | ~ r1_orders_2(A_515,C_516,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_515))
      | ~ r1_orders_2(A_515,B_514,C_516)
      | ~ m1_subset_1(C_516,u1_struct_0(A_515))
      | ~ m1_subset_1(B_514,u1_struct_0(A_515))
      | ~ l1_orders_2(A_515) ) ),
    inference(resolution,[status(thm)],[c_389,c_1726])).

tff(c_3083,plain,(
    ! [B_599,A_600] :
      ( r2_hidden(k4_tarski(B_599,'#skF_7'),u1_orders_2(A_600))
      | ~ r2_hidden(B_599,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(u1_orders_2(A_600),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2(A_600))
      | ~ r1_orders_2(A_600,'#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_600))
      | ~ r1_orders_2(A_600,B_599,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_600))
      | ~ m1_subset_1(B_599,u1_struct_0(A_600))
      | ~ l1_orders_2(A_600) ) ),
    inference(resolution,[status(thm)],[c_370,c_1899])).

tff(c_3086,plain,(
    ! [B_599] :
      ( r2_hidden(k4_tarski(B_599,'#skF_7'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(B_599,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_4','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_599,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_599,u1_struct_0('#skF_4'))
      | ~ v4_orders_2('#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_3083])).

tff(c_3089,plain,(
    ! [B_599] :
      ( r2_hidden(k4_tarski(B_599,'#skF_7'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(B_599,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_599,'#skF_6')
      | ~ m1_subset_1(B_599,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_44,c_42,c_38,c_3086])).

tff(c_3090,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3089])).

tff(c_3093,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_3090])).

tff(c_3097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3093])).

tff(c_3100,plain,(
    ! [B_601] :
      ( r2_hidden(k4_tarski(B_601,'#skF_7'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(B_601,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_601,'#skF_6')
      | ~ m1_subset_1(B_601,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_3089])).

tff(c_30,plain,(
    ! [A_37,B_41,C_43] :
      ( r1_orders_2(A_37,B_41,C_43)
      | ~ r2_hidden(k4_tarski(B_41,C_43),u1_orders_2(A_37))
      | ~ m1_subset_1(C_43,u1_struct_0(A_37))
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3121,plain,(
    ! [B_601] :
      ( r1_orders_2('#skF_4',B_601,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden(B_601,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_601,'#skF_6')
      | ~ m1_subset_1(B_601,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_3100,c_30])).

tff(c_3141,plain,(
    ! [B_602] :
      ( r1_orders_2('#skF_4',B_602,'#skF_7')
      | ~ r2_hidden(B_602,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_602,'#skF_6')
      | ~ m1_subset_1(B_602,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_3121])).

tff(c_3242,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_7')
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_367,c_3141])).

tff(c_3344,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_3242])).

tff(c_3346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_3344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:14:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.72/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.72/2.84  
% 7.72/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.72/2.84  %$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 7.72/2.84  
% 7.72/2.84  %Foreground sorts:
% 7.72/2.84  
% 7.72/2.84  
% 7.72/2.84  %Background operators:
% 7.72/2.84  
% 7.72/2.84  
% 7.72/2.84  %Foreground operators:
% 7.72/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.72/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.72/2.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.72/2.84  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.72/2.84  tff('#skF_7', type, '#skF_7': $i).
% 7.72/2.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.72/2.84  tff('#skF_5', type, '#skF_5': $i).
% 7.72/2.84  tff('#skF_6', type, '#skF_6': $i).
% 7.72/2.84  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.72/2.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.72/2.84  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.72/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.72/2.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.72/2.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.72/2.84  tff('#skF_4', type, '#skF_4': $i).
% 7.72/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.72/2.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.72/2.84  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 7.72/2.84  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 7.72/2.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.72/2.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.72/2.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.72/2.84  
% 8.08/2.87  tff(f_102, negated_conjecture, ~(![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_orders_2)).
% 8.08/2.87  tff(f_82, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 8.08/2.87  tff(f_78, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 8.08/2.87  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 8.08/2.87  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.08/2.87  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.08/2.87  tff(f_66, axiom, (![A]: (l1_orders_2(A) => (v4_orders_2(A) <=> r8_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_2)).
% 8.08/2.87  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (r8_relat_2(A, B) <=> (![C, D, E]: (((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(E, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, E), A)) => r2_hidden(k4_tarski(C, E), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_2)).
% 8.08/2.87  tff(c_36, plain, (~r1_orders_2('#skF_4', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.08/2.87  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.08/2.87  tff(c_40, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.08/2.87  tff(c_48, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.08/2.87  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.08/2.87  tff(c_34, plain, (![A_44]: (m1_subset_1(u1_orders_2(A_44), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_44), u1_struct_0(A_44)))) | ~l1_orders_2(A_44))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.08/2.87  tff(c_133, plain, (![B_96, C_97, A_98]: (r2_hidden(k4_tarski(B_96, C_97), u1_orders_2(A_98)) | ~r1_orders_2(A_98, B_96, C_97) | ~m1_subset_1(C_97, u1_struct_0(A_98)) | ~m1_subset_1(B_96, u1_struct_0(A_98)) | ~l1_orders_2(A_98))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.08/2.87  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.08/2.87  tff(c_303, plain, (![B_176, C_177, A_178, A_179]: (r2_hidden(k4_tarski(B_176, C_177), A_178) | ~m1_subset_1(u1_orders_2(A_179), k1_zfmisc_1(A_178)) | ~r1_orders_2(A_179, B_176, C_177) | ~m1_subset_1(C_177, u1_struct_0(A_179)) | ~m1_subset_1(B_176, u1_struct_0(A_179)) | ~l1_orders_2(A_179))), inference(resolution, [status(thm)], [c_133, c_8])).
% 8.08/2.87  tff(c_340, plain, (![B_208, C_209, A_210]: (r2_hidden(k4_tarski(B_208, C_209), k2_zfmisc_1(u1_struct_0(A_210), u1_struct_0(A_210))) | ~r1_orders_2(A_210, B_208, C_209) | ~m1_subset_1(C_209, u1_struct_0(A_210)) | ~m1_subset_1(B_208, u1_struct_0(A_210)) | ~l1_orders_2(A_210))), inference(resolution, [status(thm)], [c_34, c_303])).
% 8.08/2.87  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.08/2.87  tff(c_360, plain, (![B_211, A_212, C_213]: (r2_hidden(B_211, u1_struct_0(A_212)) | ~r1_orders_2(A_212, B_211, C_213) | ~m1_subset_1(C_213, u1_struct_0(A_212)) | ~m1_subset_1(B_211, u1_struct_0(A_212)) | ~l1_orders_2(A_212))), inference(resolution, [status(thm)], [c_340, c_6])).
% 8.08/2.87  tff(c_362, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_40, c_360])).
% 8.08/2.87  tff(c_367, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_362])).
% 8.08/2.87  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.08/2.87  tff(c_73, plain, (![A_78]: (m1_subset_1(u1_orders_2(A_78), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78), u1_struct_0(A_78)))) | ~l1_orders_2(A_78))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.08/2.87  tff(c_10, plain, (![C_11, A_9, B_10]: (v1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.08/2.87  tff(c_77, plain, (![A_78]: (v1_relat_1(u1_orders_2(A_78)) | ~l1_orders_2(A_78))), inference(resolution, [status(thm)], [c_73, c_10])).
% 8.08/2.87  tff(c_50, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.08/2.87  tff(c_38, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.08/2.87  tff(c_28, plain, (![A_36]: (r8_relat_2(u1_orders_2(A_36), u1_struct_0(A_36)) | ~v4_orders_2(A_36) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.08/2.87  tff(c_364, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_38, c_360])).
% 8.08/2.87  tff(c_370, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_42, c_364])).
% 8.08/2.87  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.08/2.87  tff(c_379, plain, (![C_216, A_217, B_218]: (r2_hidden(C_216, u1_struct_0(A_217)) | ~r1_orders_2(A_217, B_218, C_216) | ~m1_subset_1(C_216, u1_struct_0(A_217)) | ~m1_subset_1(B_218, u1_struct_0(A_217)) | ~l1_orders_2(A_217))), inference(resolution, [status(thm)], [c_340, c_4])).
% 8.08/2.87  tff(c_383, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_38, c_379])).
% 8.08/2.87  tff(c_389, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_42, c_383])).
% 8.08/2.87  tff(c_32, plain, (![B_41, C_43, A_37]: (r2_hidden(k4_tarski(B_41, C_43), u1_orders_2(A_37)) | ~r1_orders_2(A_37, B_41, C_43) | ~m1_subset_1(C_43, u1_struct_0(A_37)) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.08/2.87  tff(c_201, plain, (![B_133, C_132, E_130, A_131, D_129]: (r2_hidden(k4_tarski(C_132, E_130), A_131) | ~r2_hidden(k4_tarski(D_129, E_130), A_131) | ~r2_hidden(k4_tarski(C_132, D_129), A_131) | ~r2_hidden(E_130, B_133) | ~r2_hidden(D_129, B_133) | ~r2_hidden(C_132, B_133) | ~r8_relat_2(A_131, B_133) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.08/2.87  tff(c_1135, plain, (![B_386, C_383, A_384, C_385, B_387]: (r2_hidden(k4_tarski(C_383, C_385), u1_orders_2(A_384)) | ~r2_hidden(k4_tarski(C_383, B_387), u1_orders_2(A_384)) | ~r2_hidden(C_385, B_386) | ~r2_hidden(B_387, B_386) | ~r2_hidden(C_383, B_386) | ~r8_relat_2(u1_orders_2(A_384), B_386) | ~v1_relat_1(u1_orders_2(A_384)) | ~r1_orders_2(A_384, B_387, C_385) | ~m1_subset_1(C_385, u1_struct_0(A_384)) | ~m1_subset_1(B_387, u1_struct_0(A_384)) | ~l1_orders_2(A_384))), inference(resolution, [status(thm)], [c_32, c_201])).
% 8.08/2.87  tff(c_1726, plain, (![B_508, C_506, A_505, B_507, C_504]: (r2_hidden(k4_tarski(B_508, C_504), u1_orders_2(A_505)) | ~r2_hidden(C_504, B_507) | ~r2_hidden(C_506, B_507) | ~r2_hidden(B_508, B_507) | ~r8_relat_2(u1_orders_2(A_505), B_507) | ~v1_relat_1(u1_orders_2(A_505)) | ~r1_orders_2(A_505, C_506, C_504) | ~m1_subset_1(C_504, u1_struct_0(A_505)) | ~r1_orders_2(A_505, B_508, C_506) | ~m1_subset_1(C_506, u1_struct_0(A_505)) | ~m1_subset_1(B_508, u1_struct_0(A_505)) | ~l1_orders_2(A_505))), inference(resolution, [status(thm)], [c_32, c_1135])).
% 8.08/2.87  tff(c_1899, plain, (![B_514, A_515, C_516]: (r2_hidden(k4_tarski(B_514, '#skF_7'), u1_orders_2(A_515)) | ~r2_hidden(C_516, u1_struct_0('#skF_4')) | ~r2_hidden(B_514, u1_struct_0('#skF_4')) | ~r8_relat_2(u1_orders_2(A_515), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_orders_2(A_515)) | ~r1_orders_2(A_515, C_516, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0(A_515)) | ~r1_orders_2(A_515, B_514, C_516) | ~m1_subset_1(C_516, u1_struct_0(A_515)) | ~m1_subset_1(B_514, u1_struct_0(A_515)) | ~l1_orders_2(A_515))), inference(resolution, [status(thm)], [c_389, c_1726])).
% 8.08/2.87  tff(c_3083, plain, (![B_599, A_600]: (r2_hidden(k4_tarski(B_599, '#skF_7'), u1_orders_2(A_600)) | ~r2_hidden(B_599, u1_struct_0('#skF_4')) | ~r8_relat_2(u1_orders_2(A_600), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_orders_2(A_600)) | ~r1_orders_2(A_600, '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0(A_600)) | ~r1_orders_2(A_600, B_599, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(A_600)) | ~m1_subset_1(B_599, u1_struct_0(A_600)) | ~l1_orders_2(A_600))), inference(resolution, [status(thm)], [c_370, c_1899])).
% 8.08/2.87  tff(c_3086, plain, (![B_599]: (r2_hidden(k4_tarski(B_599, '#skF_7'), u1_orders_2('#skF_4')) | ~r2_hidden(B_599, u1_struct_0('#skF_4')) | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~r1_orders_2('#skF_4', B_599, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(B_599, u1_struct_0('#skF_4')) | ~v4_orders_2('#skF_4') | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_3083])).
% 8.08/2.87  tff(c_3089, plain, (![B_599]: (r2_hidden(k4_tarski(B_599, '#skF_7'), u1_orders_2('#skF_4')) | ~r2_hidden(B_599, u1_struct_0('#skF_4')) | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', B_599, '#skF_6') | ~m1_subset_1(B_599, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_44, c_42, c_38, c_3086])).
% 8.08/2.87  tff(c_3090, plain, (~v1_relat_1(u1_orders_2('#skF_4'))), inference(splitLeft, [status(thm)], [c_3089])).
% 8.08/2.87  tff(c_3093, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_77, c_3090])).
% 8.08/2.87  tff(c_3097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_3093])).
% 8.08/2.87  tff(c_3100, plain, (![B_601]: (r2_hidden(k4_tarski(B_601, '#skF_7'), u1_orders_2('#skF_4')) | ~r2_hidden(B_601, u1_struct_0('#skF_4')) | ~r1_orders_2('#skF_4', B_601, '#skF_6') | ~m1_subset_1(B_601, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_3089])).
% 8.08/2.87  tff(c_30, plain, (![A_37, B_41, C_43]: (r1_orders_2(A_37, B_41, C_43) | ~r2_hidden(k4_tarski(B_41, C_43), u1_orders_2(A_37)) | ~m1_subset_1(C_43, u1_struct_0(A_37)) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.08/2.87  tff(c_3121, plain, (![B_601]: (r1_orders_2('#skF_4', B_601, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden(B_601, u1_struct_0('#skF_4')) | ~r1_orders_2('#skF_4', B_601, '#skF_6') | ~m1_subset_1(B_601, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3100, c_30])).
% 8.08/2.87  tff(c_3141, plain, (![B_602]: (r1_orders_2('#skF_4', B_602, '#skF_7') | ~r2_hidden(B_602, u1_struct_0('#skF_4')) | ~r1_orders_2('#skF_4', B_602, '#skF_6') | ~m1_subset_1(B_602, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_3121])).
% 8.08/2.87  tff(c_3242, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_7') | ~r1_orders_2('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_367, c_3141])).
% 8.08/2.87  tff(c_3344, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_3242])).
% 8.08/2.87  tff(c_3346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_3344])).
% 8.08/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.87  
% 8.08/2.87  Inference rules
% 8.08/2.87  ----------------------
% 8.08/2.87  #Ref     : 0
% 8.08/2.87  #Sup     : 891
% 8.08/2.87  #Fact    : 0
% 8.08/2.87  #Define  : 0
% 8.08/2.87  #Split   : 1
% 8.08/2.87  #Chain   : 0
% 8.08/2.87  #Close   : 0
% 8.08/2.87  
% 8.08/2.87  Ordering : KBO
% 8.08/2.87  
% 8.08/2.87  Simplification rules
% 8.08/2.87  ----------------------
% 8.08/2.87  #Subsume      : 142
% 8.08/2.87  #Demod        : 39
% 8.08/2.87  #Tautology    : 18
% 8.08/2.87  #SimpNegUnit  : 1
% 8.08/2.87  #BackRed      : 0
% 8.08/2.87  
% 8.08/2.87  #Partial instantiations: 0
% 8.08/2.87  #Strategies tried      : 1
% 8.08/2.87  
% 8.08/2.87  Timing (in seconds)
% 8.08/2.87  ----------------------
% 8.08/2.87  Preprocessing        : 0.37
% 8.08/2.87  Parsing              : 0.21
% 8.08/2.87  CNF conversion       : 0.03
% 8.08/2.87  Main loop            : 1.67
% 8.08/2.87  Inferencing          : 0.49
% 8.08/2.87  Reduction            : 0.35
% 8.08/2.87  Demodulation         : 0.23
% 8.08/2.87  BG Simplification    : 0.06
% 8.08/2.87  Subsumption          : 0.66
% 8.08/2.87  Abstraction          : 0.08
% 8.08/2.87  MUC search           : 0.00
% 8.08/2.87  Cooper               : 0.00
% 8.08/2.87  Total                : 2.08
% 8.08/2.87  Index Insertion      : 0.00
% 8.08/2.87  Index Deletion       : 0.00
% 8.08/2.87  Index Matching       : 0.00
% 8.08/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
