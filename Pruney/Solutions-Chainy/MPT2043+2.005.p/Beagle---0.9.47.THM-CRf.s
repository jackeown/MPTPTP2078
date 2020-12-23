%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:23 EST 2020

% Result     : Theorem 9.14s
% Output     : CNFRefutation 9.24s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 617 expanded)
%              Number of leaves         :   42 ( 220 expanded)
%              Depth                    :   18
%              Number of atoms          :  236 (1446 expanded)
%              Number of equality atoms :   36 ( 264 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_76,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_74,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
              & v2_waybel_0(B,k3_yellow_1(A))
              & v13_waybel_0(B,k3_yellow_1(A))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
           => ! [C] :
                ~ ( r2_hidden(C,B)
                  & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))
     => ( v13_waybel_0(B,k3_yellow_1(A))
      <=> ! [C,D] :
            ( ( r1_tarski(C,D)
              & r1_tarski(D,A)
              & r2_hidden(C,B) )
           => r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(c_30,plain,(
    ! [A_19] : ~ v1_subset_1('#skF_6'(A_19),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [A_19] : m1_subset_1('#skF_6'(A_19),k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_250,plain,(
    ! [B_75,A_76] :
      ( v1_subset_1(B_75,A_76)
      | B_75 = A_76
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_256,plain,(
    ! [A_19] :
      ( v1_subset_1('#skF_6'(A_19),A_19)
      | '#skF_6'(A_19) = A_19 ) ),
    inference(resolution,[status(thm)],[c_32,c_250])).

tff(c_261,plain,(
    ! [A_19] : '#skF_6'(A_19) = A_19 ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_256])).

tff(c_269,plain,(
    ! [A_19] : ~ v1_subset_1(A_19,A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_30])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_187,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden('#skF_2'(A_65,B_66),B_66)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_201,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_187])).

tff(c_36,plain,(
    ! [A_23] : k9_setfam_1(A_23) = k1_zfmisc_1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    ! [A_25] : k2_yellow_1(k9_setfam_1(A_25)) = k3_yellow_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_108,plain,(
    ! [A_47] : k2_yellow_1(k1_zfmisc_1(A_47)) = k3_yellow_1(A_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42])).

tff(c_38,plain,(
    ! [A_24] : u1_struct_0(k2_yellow_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_117,plain,(
    ! [A_47] : u1_struct_0(k3_yellow_1(A_47)) = k1_zfmisc_1(A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_38])).

tff(c_62,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_139,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_62])).

tff(c_176,plain,(
    ! [A_61,B_62] :
      ( r2_hidden(A_61,B_62)
      | v1_xboole_0(B_62)
      | ~ m1_subset_1(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_392,plain,(
    ! [A_101,A_102] :
      ( r1_tarski(A_101,A_102)
      | v1_xboole_0(k1_zfmisc_1(A_102))
      | ~ m1_subset_1(A_101,k1_zfmisc_1(A_102)) ) ),
    inference(resolution,[status(thm)],[c_176,c_14])).

tff(c_406,plain,
    ( r1_tarski('#skF_10',k1_zfmisc_1('#skF_9'))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_139,c_392])).

tff(c_418,plain,(
    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_150,plain,(
    ! [C_53,A_54] :
      ( r2_hidden(C_53,k1_zfmisc_1(A_54))
      | ~ r1_tarski(C_53,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [A_54,C_53] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_54))
      | ~ r1_tarski(C_53,A_54) ) ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_422,plain,(
    ! [C_105] : ~ r1_tarski(C_105,k1_zfmisc_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_418,c_154])).

tff(c_444,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_201,c_422])).

tff(c_445,plain,(
    r1_tarski('#skF_10',k1_zfmisc_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_268,plain,(
    ! [A_19] : m1_subset_1(A_19,k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_32])).

tff(c_64,plain,(
    v13_waybel_0('#skF_10',k3_yellow_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_204,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_306,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_1'(A_84),B_85)
      | ~ r1_tarski(A_84,B_85)
      | v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_4,c_204])).

tff(c_319,plain,(
    ! [B_86,A_87] :
      ( ~ v1_xboole_0(B_86)
      | ~ r1_tarski(A_87,B_86)
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_306,c_2])).

tff(c_335,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(A_10)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_319])).

tff(c_336,plain,(
    ! [A_10] : ~ v1_xboole_0(A_10) ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_58,plain,(
    v1_xboole_0('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_58])).

tff(c_355,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_166,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_2'(A_59,B_60),A_59)
      | r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_175,plain,(
    ! [A_59,B_60] :
      ( ~ v1_xboole_0(A_59)
      | r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_166,c_2])).

tff(c_60,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    ! [D_35,B_29,C_34,A_28] :
      ( r2_hidden(D_35,B_29)
      | ~ r2_hidden(C_34,B_29)
      | ~ r1_tarski(D_35,A_28)
      | ~ r1_tarski(C_34,D_35)
      | ~ v13_waybel_0(B_29,k3_yellow_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_28)))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1642,plain,(
    ! [D_212,B_213,C_214,A_215] :
      ( r2_hidden(D_212,B_213)
      | ~ r2_hidden(C_214,B_213)
      | ~ r1_tarski(D_212,A_215)
      | ~ r1_tarski(C_214,D_212)
      | ~ v13_waybel_0(B_213,k3_yellow_1(A_215))
      | ~ m1_subset_1(B_213,k1_zfmisc_1(k1_zfmisc_1(A_215))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_48])).

tff(c_1782,plain,(
    ! [D_219,A_220] :
      ( r2_hidden(D_219,'#skF_10')
      | ~ r1_tarski(D_219,A_220)
      | ~ r1_tarski('#skF_11',D_219)
      | ~ v13_waybel_0('#skF_10',k3_yellow_1(A_220))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(A_220))) ) ),
    inference(resolution,[status(thm)],[c_60,c_1642])).

tff(c_1840,plain,(
    ! [A_10] :
      ( r2_hidden(k1_xboole_0,'#skF_10')
      | ~ r1_tarski('#skF_11',k1_xboole_0)
      | ~ v13_waybel_0('#skF_10',k3_yellow_1(A_10))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1782])).

tff(c_2188,plain,(
    ~ r1_tarski('#skF_11',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1840])).

tff(c_2191,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_175,c_2188])).

tff(c_2195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2191])).

tff(c_2197,plain,(
    r1_tarski('#skF_11',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1840])).

tff(c_545,plain,(
    ! [A_117,B_118,B_119] :
      ( r2_hidden('#skF_2'(A_117,B_118),B_119)
      | ~ r1_tarski(A_117,B_119)
      | r1_tarski(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_10,c_204])).

tff(c_562,plain,(
    ! [B_119,A_117,B_118] :
      ( ~ v1_xboole_0(B_119)
      | ~ r1_tarski(A_117,B_119)
      | r1_tarski(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_545,c_2])).

tff(c_2216,plain,(
    ! [B_118] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_tarski('#skF_11',B_118) ) ),
    inference(resolution,[status(thm)],[c_2197,c_562])).

tff(c_2239,plain,(
    ! [B_118] : r1_tarski('#skF_11',B_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_2216])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski('#skF_3'(A_11,B_12),A_11)
      | r2_hidden('#skF_4'(A_11,B_12),B_12)
      | k1_zfmisc_1(A_11) = B_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1832,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),'#skF_10')
      | ~ r1_tarski('#skF_11','#skF_3'(A_11,B_12))
      | ~ v13_waybel_0('#skF_10',k3_yellow_1(A_11))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(A_11)))
      | r2_hidden('#skF_4'(A_11,B_12),B_12)
      | k1_zfmisc_1(A_11) = B_12 ) ),
    inference(resolution,[status(thm)],[c_24,c_1782])).

tff(c_6975,plain,(
    ! [A_381,B_382] :
      ( r2_hidden('#skF_3'(A_381,B_382),'#skF_10')
      | ~ v13_waybel_0('#skF_10',k3_yellow_1(A_381))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(A_381)))
      | r2_hidden('#skF_4'(A_381,B_382),B_382)
      | k1_zfmisc_1(A_381) = B_382 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2239,c_1832])).

tff(c_6977,plain,(
    ! [B_382] :
      ( r2_hidden('#skF_3'('#skF_9',B_382),'#skF_10')
      | ~ v13_waybel_0('#skF_10',k3_yellow_1('#skF_9'))
      | r2_hidden('#skF_4'('#skF_9',B_382),B_382)
      | k1_zfmisc_1('#skF_9') = B_382 ) ),
    inference(resolution,[status(thm)],[c_139,c_6975])).

tff(c_12733,plain,(
    ! [B_491] :
      ( r2_hidden('#skF_3'('#skF_9',B_491),'#skF_10')
      | r2_hidden('#skF_4'('#skF_9',B_491),B_491)
      | k1_zfmisc_1('#skF_9') = B_491 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6977])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r2_hidden('#skF_4'(A_11,B_12),B_12)
      | k1_zfmisc_1(A_11) = B_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12761,plain,
    ( r2_hidden('#skF_4'('#skF_9','#skF_10'),'#skF_10')
    | k1_zfmisc_1('#skF_9') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_12733,c_22])).

tff(c_12768,plain,(
    k1_zfmisc_1('#skF_9') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_12761])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1('#skF_5'(A_16,B_17),A_16)
      | B_17 = A_16
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_617,plain,(
    ! [A_127,B_128,B_129] :
      ( r2_hidden(A_127,B_128)
      | ~ r1_tarski(B_129,B_128)
      | v1_xboole_0(B_129)
      | ~ m1_subset_1(A_127,B_129) ) ),
    inference(resolution,[status(thm)],[c_34,c_204])).

tff(c_629,plain,(
    ! [A_127] :
      ( r2_hidden(A_127,k1_zfmisc_1('#skF_9'))
      | v1_xboole_0('#skF_10')
      | ~ m1_subset_1(A_127,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_445,c_617])).

tff(c_655,plain,(
    ! [A_130] :
      ( r2_hidden(A_130,k1_zfmisc_1('#skF_9'))
      | ~ m1_subset_1(A_130,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_629])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( ~ r2_hidden('#skF_5'(A_16,B_17),B_17)
      | B_17 = A_16
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_764,plain,(
    ! [A_138] :
      ( k1_zfmisc_1('#skF_9') = A_138
      | ~ m1_subset_1(k1_zfmisc_1('#skF_9'),k1_zfmisc_1(A_138))
      | ~ m1_subset_1('#skF_5'(A_138,k1_zfmisc_1('#skF_9')),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_655,c_26])).

tff(c_769,plain,
    ( k1_zfmisc_1('#skF_9') = '#skF_10'
    | ~ m1_subset_1(k1_zfmisc_1('#skF_9'),k1_zfmisc_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_28,c_764])).

tff(c_770,plain,(
    ~ m1_subset_1(k1_zfmisc_1('#skF_9'),k1_zfmisc_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_769])).

tff(c_12782,plain,(
    ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12768,c_770])).

tff(c_12793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_12782])).

tff(c_12794,plain,(
    r2_hidden('#skF_4'('#skF_9','#skF_10'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_12761])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12806,plain,(
    ! [B_492] :
      ( r2_hidden('#skF_4'('#skF_9','#skF_10'),B_492)
      | ~ r1_tarski('#skF_10',B_492) ) ),
    inference(resolution,[status(thm)],[c_12794,c_6])).

tff(c_12820,plain,(
    ! [A_11] :
      ( r1_tarski('#skF_4'('#skF_9','#skF_10'),A_11)
      | ~ r1_tarski('#skF_10',k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_12806,c_14])).

tff(c_12795,plain,(
    k1_zfmisc_1('#skF_9') != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_12761])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r1_tarski('#skF_3'(A_11,B_12),A_11)
      | ~ r1_tarski('#skF_4'(A_11,B_12),A_11)
      | k1_zfmisc_1(A_11) = B_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1826,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),'#skF_10')
      | ~ r1_tarski('#skF_11','#skF_3'(A_11,B_12))
      | ~ v13_waybel_0('#skF_10',k3_yellow_1(A_11))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(A_11)))
      | ~ r1_tarski('#skF_4'(A_11,B_12),A_11)
      | k1_zfmisc_1(A_11) = B_12 ) ),
    inference(resolution,[status(thm)],[c_20,c_1782])).

tff(c_6628,plain,(
    ! [A_368,B_369] :
      ( r2_hidden('#skF_3'(A_368,B_369),'#skF_10')
      | ~ v13_waybel_0('#skF_10',k3_yellow_1(A_368))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k1_zfmisc_1(A_368)))
      | ~ r1_tarski('#skF_4'(A_368,B_369),A_368)
      | k1_zfmisc_1(A_368) = B_369 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2239,c_1826])).

tff(c_6630,plain,(
    ! [B_369] :
      ( r2_hidden('#skF_3'('#skF_9',B_369),'#skF_10')
      | ~ v13_waybel_0('#skF_10',k3_yellow_1('#skF_9'))
      | ~ r1_tarski('#skF_4'('#skF_9',B_369),'#skF_9')
      | k1_zfmisc_1('#skF_9') = B_369 ) ),
    inference(resolution,[status(thm)],[c_139,c_6628])).

tff(c_13158,plain,(
    ! [B_505] :
      ( r2_hidden('#skF_3'('#skF_9',B_505),'#skF_10')
      | ~ r1_tarski('#skF_4'('#skF_9',B_505),'#skF_9')
      | k1_zfmisc_1('#skF_9') = B_505 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6630])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_3'(A_11,B_12),B_12)
      | ~ r1_tarski('#skF_4'(A_11,B_12),A_11)
      | k1_zfmisc_1(A_11) = B_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13163,plain,
    ( ~ r1_tarski('#skF_4'('#skF_9','#skF_10'),'#skF_9')
    | k1_zfmisc_1('#skF_9') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_13158,c_18])).

tff(c_13176,plain,(
    ~ r1_tarski('#skF_4'('#skF_9','#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_12795,c_12795,c_13163])).

tff(c_13184,plain,(
    ~ r1_tarski('#skF_10',k1_zfmisc_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_12820,c_13176])).

tff(c_13195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_13184])).

tff(c_13196,plain,(
    k1_zfmisc_1('#skF_9') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_769])).

tff(c_68,plain,(
    v1_subset_1('#skF_10',u1_struct_0(k3_yellow_1('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_129,plain,(
    v1_subset_1('#skF_10',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_68])).

tff(c_13209,plain,(
    v1_subset_1('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13196,c_129])).

tff(c_13214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_13209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.14/3.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.14/3.38  
% 9.14/3.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.24/3.38  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4
% 9.24/3.38  
% 9.24/3.38  %Foreground sorts:
% 9.24/3.38  
% 9.24/3.38  
% 9.24/3.38  %Background operators:
% 9.24/3.38  
% 9.24/3.38  
% 9.24/3.38  %Foreground operators:
% 9.24/3.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.24/3.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.24/3.38  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 9.24/3.38  tff('#skF_11', type, '#skF_11': $i).
% 9.24/3.38  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 9.24/3.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.24/3.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.24/3.38  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 9.24/3.38  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 9.24/3.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.24/3.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.24/3.38  tff('#skF_10', type, '#skF_10': $i).
% 9.24/3.38  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 9.24/3.38  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 9.24/3.38  tff('#skF_9', type, '#skF_9': $i).
% 9.24/3.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.24/3.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.24/3.38  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 9.24/3.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.24/3.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.24/3.38  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 9.24/3.38  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 9.24/3.38  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 9.24/3.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.24/3.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.24/3.38  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.24/3.38  tff('#skF_6', type, '#skF_6': $i > $i).
% 9.24/3.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.24/3.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.24/3.38  
% 9.24/3.40  tff(f_62, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 9.24/3.40  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 9.24/3.40  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.24/3.40  tff(f_70, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 9.24/3.40  tff(f_76, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 9.24/3.40  tff(f_74, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 9.24/3.40  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 9.24/3.40  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.24/3.40  tff(f_47, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.24/3.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.24/3.40  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.24/3.40  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) => (v13_waybel_0(B, k3_yellow_1(A)) <=> (![C, D]: (((r1_tarski(C, D) & r1_tarski(D, A)) & r2_hidden(C, B)) => r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_waybel_7)).
% 9.24/3.40  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 9.24/3.40  tff(c_30, plain, (![A_19]: (~v1_subset_1('#skF_6'(A_19), A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.24/3.40  tff(c_32, plain, (![A_19]: (m1_subset_1('#skF_6'(A_19), k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.24/3.40  tff(c_250, plain, (![B_75, A_76]: (v1_subset_1(B_75, A_76) | B_75=A_76 | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.24/3.40  tff(c_256, plain, (![A_19]: (v1_subset_1('#skF_6'(A_19), A_19) | '#skF_6'(A_19)=A_19)), inference(resolution, [status(thm)], [c_32, c_250])).
% 9.24/3.40  tff(c_261, plain, (![A_19]: ('#skF_6'(A_19)=A_19)), inference(negUnitSimplification, [status(thm)], [c_30, c_256])).
% 9.24/3.40  tff(c_269, plain, (![A_19]: (~v1_subset_1(A_19, A_19))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_30])).
% 9.24/3.40  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.24/3.40  tff(c_187, plain, (![A_65, B_66]: (~r2_hidden('#skF_2'(A_65, B_66), B_66) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.24/3.40  tff(c_201, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_187])).
% 9.24/3.40  tff(c_36, plain, (![A_23]: (k9_setfam_1(A_23)=k1_zfmisc_1(A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.24/3.40  tff(c_42, plain, (![A_25]: (k2_yellow_1(k9_setfam_1(A_25))=k3_yellow_1(A_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.24/3.40  tff(c_108, plain, (![A_47]: (k2_yellow_1(k1_zfmisc_1(A_47))=k3_yellow_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_42])).
% 9.24/3.40  tff(c_38, plain, (![A_24]: (u1_struct_0(k2_yellow_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.24/3.40  tff(c_117, plain, (![A_47]: (u1_struct_0(k3_yellow_1(A_47))=k1_zfmisc_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_108, c_38])).
% 9.24/3.40  tff(c_62, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.24/3.40  tff(c_139, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k1_zfmisc_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_62])).
% 9.24/3.40  tff(c_176, plain, (![A_61, B_62]: (r2_hidden(A_61, B_62) | v1_xboole_0(B_62) | ~m1_subset_1(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.24/3.40  tff(c_14, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.24/3.40  tff(c_392, plain, (![A_101, A_102]: (r1_tarski(A_101, A_102) | v1_xboole_0(k1_zfmisc_1(A_102)) | ~m1_subset_1(A_101, k1_zfmisc_1(A_102)))), inference(resolution, [status(thm)], [c_176, c_14])).
% 9.24/3.40  tff(c_406, plain, (r1_tarski('#skF_10', k1_zfmisc_1('#skF_9')) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1('#skF_9')))), inference(resolution, [status(thm)], [c_139, c_392])).
% 9.24/3.40  tff(c_418, plain, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1('#skF_9')))), inference(splitLeft, [status(thm)], [c_406])).
% 9.24/3.40  tff(c_150, plain, (![C_53, A_54]: (r2_hidden(C_53, k1_zfmisc_1(A_54)) | ~r1_tarski(C_53, A_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.24/3.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.24/3.40  tff(c_154, plain, (![A_54, C_53]: (~v1_xboole_0(k1_zfmisc_1(A_54)) | ~r1_tarski(C_53, A_54))), inference(resolution, [status(thm)], [c_150, c_2])).
% 9.24/3.40  tff(c_422, plain, (![C_105]: (~r1_tarski(C_105, k1_zfmisc_1('#skF_9')))), inference(resolution, [status(thm)], [c_418, c_154])).
% 9.24/3.40  tff(c_444, plain, $false, inference(resolution, [status(thm)], [c_201, c_422])).
% 9.24/3.40  tff(c_445, plain, (r1_tarski('#skF_10', k1_zfmisc_1('#skF_9'))), inference(splitRight, [status(thm)], [c_406])).
% 9.24/3.40  tff(c_268, plain, (![A_19]: (m1_subset_1(A_19, k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_32])).
% 9.24/3.40  tff(c_64, plain, (v13_waybel_0('#skF_10', k3_yellow_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.24/3.40  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.24/3.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.24/3.40  tff(c_204, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.24/3.40  tff(c_306, plain, (![A_84, B_85]: (r2_hidden('#skF_1'(A_84), B_85) | ~r1_tarski(A_84, B_85) | v1_xboole_0(A_84))), inference(resolution, [status(thm)], [c_4, c_204])).
% 9.24/3.40  tff(c_319, plain, (![B_86, A_87]: (~v1_xboole_0(B_86) | ~r1_tarski(A_87, B_86) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_306, c_2])).
% 9.24/3.40  tff(c_335, plain, (![A_10]: (~v1_xboole_0(A_10) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_319])).
% 9.24/3.40  tff(c_336, plain, (![A_10]: (~v1_xboole_0(A_10))), inference(splitLeft, [status(thm)], [c_335])).
% 9.24/3.40  tff(c_58, plain, (v1_xboole_0('#skF_11')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.24/3.40  tff(c_354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_58])).
% 9.24/3.40  tff(c_355, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_335])).
% 9.24/3.40  tff(c_166, plain, (![A_59, B_60]: (r2_hidden('#skF_2'(A_59, B_60), A_59) | r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.24/3.40  tff(c_175, plain, (![A_59, B_60]: (~v1_xboole_0(A_59) | r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_166, c_2])).
% 9.24/3.40  tff(c_60, plain, (r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.24/3.40  tff(c_48, plain, (![D_35, B_29, C_34, A_28]: (r2_hidden(D_35, B_29) | ~r2_hidden(C_34, B_29) | ~r1_tarski(D_35, A_28) | ~r1_tarski(C_34, D_35) | ~v13_waybel_0(B_29, k3_yellow_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_28)))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.24/3.40  tff(c_1642, plain, (![D_212, B_213, C_214, A_215]: (r2_hidden(D_212, B_213) | ~r2_hidden(C_214, B_213) | ~r1_tarski(D_212, A_215) | ~r1_tarski(C_214, D_212) | ~v13_waybel_0(B_213, k3_yellow_1(A_215)) | ~m1_subset_1(B_213, k1_zfmisc_1(k1_zfmisc_1(A_215))))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_48])).
% 9.24/3.40  tff(c_1782, plain, (![D_219, A_220]: (r2_hidden(D_219, '#skF_10') | ~r1_tarski(D_219, A_220) | ~r1_tarski('#skF_11', D_219) | ~v13_waybel_0('#skF_10', k3_yellow_1(A_220)) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k1_zfmisc_1(A_220))))), inference(resolution, [status(thm)], [c_60, c_1642])).
% 9.24/3.40  tff(c_1840, plain, (![A_10]: (r2_hidden(k1_xboole_0, '#skF_10') | ~r1_tarski('#skF_11', k1_xboole_0) | ~v13_waybel_0('#skF_10', k3_yellow_1(A_10)) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(resolution, [status(thm)], [c_12, c_1782])).
% 9.24/3.40  tff(c_2188, plain, (~r1_tarski('#skF_11', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1840])).
% 9.24/3.40  tff(c_2191, plain, (~v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_175, c_2188])).
% 9.24/3.40  tff(c_2195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_2191])).
% 9.24/3.40  tff(c_2197, plain, (r1_tarski('#skF_11', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1840])).
% 9.24/3.40  tff(c_545, plain, (![A_117, B_118, B_119]: (r2_hidden('#skF_2'(A_117, B_118), B_119) | ~r1_tarski(A_117, B_119) | r1_tarski(A_117, B_118))), inference(resolution, [status(thm)], [c_10, c_204])).
% 9.24/3.40  tff(c_562, plain, (![B_119, A_117, B_118]: (~v1_xboole_0(B_119) | ~r1_tarski(A_117, B_119) | r1_tarski(A_117, B_118))), inference(resolution, [status(thm)], [c_545, c_2])).
% 9.24/3.40  tff(c_2216, plain, (![B_118]: (~v1_xboole_0(k1_xboole_0) | r1_tarski('#skF_11', B_118))), inference(resolution, [status(thm)], [c_2197, c_562])).
% 9.24/3.40  tff(c_2239, plain, (![B_118]: (r1_tarski('#skF_11', B_118))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_2216])).
% 9.24/3.40  tff(c_24, plain, (![A_11, B_12]: (r1_tarski('#skF_3'(A_11, B_12), A_11) | r2_hidden('#skF_4'(A_11, B_12), B_12) | k1_zfmisc_1(A_11)=B_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.24/3.40  tff(c_1832, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), '#skF_10') | ~r1_tarski('#skF_11', '#skF_3'(A_11, B_12)) | ~v13_waybel_0('#skF_10', k3_yellow_1(A_11)) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k1_zfmisc_1(A_11))) | r2_hidden('#skF_4'(A_11, B_12), B_12) | k1_zfmisc_1(A_11)=B_12)), inference(resolution, [status(thm)], [c_24, c_1782])).
% 9.24/3.40  tff(c_6975, plain, (![A_381, B_382]: (r2_hidden('#skF_3'(A_381, B_382), '#skF_10') | ~v13_waybel_0('#skF_10', k3_yellow_1(A_381)) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k1_zfmisc_1(A_381))) | r2_hidden('#skF_4'(A_381, B_382), B_382) | k1_zfmisc_1(A_381)=B_382)), inference(demodulation, [status(thm), theory('equality')], [c_2239, c_1832])).
% 9.24/3.40  tff(c_6977, plain, (![B_382]: (r2_hidden('#skF_3'('#skF_9', B_382), '#skF_10') | ~v13_waybel_0('#skF_10', k3_yellow_1('#skF_9')) | r2_hidden('#skF_4'('#skF_9', B_382), B_382) | k1_zfmisc_1('#skF_9')=B_382)), inference(resolution, [status(thm)], [c_139, c_6975])).
% 9.24/3.40  tff(c_12733, plain, (![B_491]: (r2_hidden('#skF_3'('#skF_9', B_491), '#skF_10') | r2_hidden('#skF_4'('#skF_9', B_491), B_491) | k1_zfmisc_1('#skF_9')=B_491)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6977])).
% 9.24/3.40  tff(c_22, plain, (![A_11, B_12]: (~r2_hidden('#skF_3'(A_11, B_12), B_12) | r2_hidden('#skF_4'(A_11, B_12), B_12) | k1_zfmisc_1(A_11)=B_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.24/3.40  tff(c_12761, plain, (r2_hidden('#skF_4'('#skF_9', '#skF_10'), '#skF_10') | k1_zfmisc_1('#skF_9')='#skF_10'), inference(resolution, [status(thm)], [c_12733, c_22])).
% 9.24/3.40  tff(c_12768, plain, (k1_zfmisc_1('#skF_9')='#skF_10'), inference(splitLeft, [status(thm)], [c_12761])).
% 9.24/3.40  tff(c_28, plain, (![A_16, B_17]: (m1_subset_1('#skF_5'(A_16, B_17), A_16) | B_17=A_16 | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.24/3.40  tff(c_70, plain, (~v1_xboole_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.24/3.40  tff(c_34, plain, (![A_21, B_22]: (r2_hidden(A_21, B_22) | v1_xboole_0(B_22) | ~m1_subset_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.24/3.40  tff(c_617, plain, (![A_127, B_128, B_129]: (r2_hidden(A_127, B_128) | ~r1_tarski(B_129, B_128) | v1_xboole_0(B_129) | ~m1_subset_1(A_127, B_129))), inference(resolution, [status(thm)], [c_34, c_204])).
% 9.24/3.40  tff(c_629, plain, (![A_127]: (r2_hidden(A_127, k1_zfmisc_1('#skF_9')) | v1_xboole_0('#skF_10') | ~m1_subset_1(A_127, '#skF_10'))), inference(resolution, [status(thm)], [c_445, c_617])).
% 9.24/3.40  tff(c_655, plain, (![A_130]: (r2_hidden(A_130, k1_zfmisc_1('#skF_9')) | ~m1_subset_1(A_130, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_70, c_629])).
% 9.24/3.40  tff(c_26, plain, (![A_16, B_17]: (~r2_hidden('#skF_5'(A_16, B_17), B_17) | B_17=A_16 | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.24/3.40  tff(c_764, plain, (![A_138]: (k1_zfmisc_1('#skF_9')=A_138 | ~m1_subset_1(k1_zfmisc_1('#skF_9'), k1_zfmisc_1(A_138)) | ~m1_subset_1('#skF_5'(A_138, k1_zfmisc_1('#skF_9')), '#skF_10'))), inference(resolution, [status(thm)], [c_655, c_26])).
% 9.24/3.40  tff(c_769, plain, (k1_zfmisc_1('#skF_9')='#skF_10' | ~m1_subset_1(k1_zfmisc_1('#skF_9'), k1_zfmisc_1('#skF_10'))), inference(resolution, [status(thm)], [c_28, c_764])).
% 9.24/3.40  tff(c_770, plain, (~m1_subset_1(k1_zfmisc_1('#skF_9'), k1_zfmisc_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_769])).
% 9.24/3.40  tff(c_12782, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_12768, c_770])).
% 9.24/3.40  tff(c_12793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_12782])).
% 9.24/3.40  tff(c_12794, plain, (r2_hidden('#skF_4'('#skF_9', '#skF_10'), '#skF_10')), inference(splitRight, [status(thm)], [c_12761])).
% 9.24/3.40  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.24/3.40  tff(c_12806, plain, (![B_492]: (r2_hidden('#skF_4'('#skF_9', '#skF_10'), B_492) | ~r1_tarski('#skF_10', B_492))), inference(resolution, [status(thm)], [c_12794, c_6])).
% 9.24/3.40  tff(c_12820, plain, (![A_11]: (r1_tarski('#skF_4'('#skF_9', '#skF_10'), A_11) | ~r1_tarski('#skF_10', k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_12806, c_14])).
% 9.24/3.40  tff(c_12795, plain, (k1_zfmisc_1('#skF_9')!='#skF_10'), inference(splitRight, [status(thm)], [c_12761])).
% 9.24/3.40  tff(c_20, plain, (![A_11, B_12]: (r1_tarski('#skF_3'(A_11, B_12), A_11) | ~r1_tarski('#skF_4'(A_11, B_12), A_11) | k1_zfmisc_1(A_11)=B_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.24/3.40  tff(c_1826, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), '#skF_10') | ~r1_tarski('#skF_11', '#skF_3'(A_11, B_12)) | ~v13_waybel_0('#skF_10', k3_yellow_1(A_11)) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k1_zfmisc_1(A_11))) | ~r1_tarski('#skF_4'(A_11, B_12), A_11) | k1_zfmisc_1(A_11)=B_12)), inference(resolution, [status(thm)], [c_20, c_1782])).
% 9.24/3.40  tff(c_6628, plain, (![A_368, B_369]: (r2_hidden('#skF_3'(A_368, B_369), '#skF_10') | ~v13_waybel_0('#skF_10', k3_yellow_1(A_368)) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k1_zfmisc_1(A_368))) | ~r1_tarski('#skF_4'(A_368, B_369), A_368) | k1_zfmisc_1(A_368)=B_369)), inference(demodulation, [status(thm), theory('equality')], [c_2239, c_1826])).
% 9.24/3.40  tff(c_6630, plain, (![B_369]: (r2_hidden('#skF_3'('#skF_9', B_369), '#skF_10') | ~v13_waybel_0('#skF_10', k3_yellow_1('#skF_9')) | ~r1_tarski('#skF_4'('#skF_9', B_369), '#skF_9') | k1_zfmisc_1('#skF_9')=B_369)), inference(resolution, [status(thm)], [c_139, c_6628])).
% 9.24/3.40  tff(c_13158, plain, (![B_505]: (r2_hidden('#skF_3'('#skF_9', B_505), '#skF_10') | ~r1_tarski('#skF_4'('#skF_9', B_505), '#skF_9') | k1_zfmisc_1('#skF_9')=B_505)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6630])).
% 9.24/3.40  tff(c_18, plain, (![A_11, B_12]: (~r2_hidden('#skF_3'(A_11, B_12), B_12) | ~r1_tarski('#skF_4'(A_11, B_12), A_11) | k1_zfmisc_1(A_11)=B_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.24/3.40  tff(c_13163, plain, (~r1_tarski('#skF_4'('#skF_9', '#skF_10'), '#skF_9') | k1_zfmisc_1('#skF_9')='#skF_10'), inference(resolution, [status(thm)], [c_13158, c_18])).
% 9.24/3.40  tff(c_13176, plain, (~r1_tarski('#skF_4'('#skF_9', '#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_12795, c_12795, c_13163])).
% 9.24/3.40  tff(c_13184, plain, (~r1_tarski('#skF_10', k1_zfmisc_1('#skF_9'))), inference(resolution, [status(thm)], [c_12820, c_13176])).
% 9.24/3.40  tff(c_13195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_445, c_13184])).
% 9.24/3.40  tff(c_13196, plain, (k1_zfmisc_1('#skF_9')='#skF_10'), inference(splitRight, [status(thm)], [c_769])).
% 9.24/3.40  tff(c_68, plain, (v1_subset_1('#skF_10', u1_struct_0(k3_yellow_1('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.24/3.40  tff(c_129, plain, (v1_subset_1('#skF_10', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_68])).
% 9.24/3.40  tff(c_13209, plain, (v1_subset_1('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_13196, c_129])).
% 9.24/3.40  tff(c_13214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_13209])).
% 9.24/3.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.24/3.40  
% 9.24/3.40  Inference rules
% 9.24/3.40  ----------------------
% 9.24/3.40  #Ref     : 0
% 9.24/3.40  #Sup     : 3199
% 9.24/3.40  #Fact    : 0
% 9.24/3.40  #Define  : 0
% 9.24/3.40  #Split   : 67
% 9.24/3.40  #Chain   : 0
% 9.24/3.40  #Close   : 0
% 9.24/3.40  
% 9.24/3.40  Ordering : KBO
% 9.24/3.40  
% 9.24/3.40  Simplification rules
% 9.24/3.40  ----------------------
% 9.24/3.41  #Subsume      : 1494
% 9.24/3.41  #Demod        : 1094
% 9.24/3.41  #Tautology    : 456
% 9.24/3.41  #SimpNegUnit  : 630
% 9.24/3.41  #BackRed      : 556
% 9.24/3.41  
% 9.24/3.41  #Partial instantiations: 0
% 9.24/3.41  #Strategies tried      : 1
% 9.24/3.41  
% 9.24/3.41  Timing (in seconds)
% 9.24/3.41  ----------------------
% 9.24/3.41  Preprocessing        : 0.32
% 9.24/3.41  Parsing              : 0.17
% 9.24/3.41  CNF conversion       : 0.02
% 9.24/3.41  Main loop            : 2.30
% 9.24/3.41  Inferencing          : 0.55
% 9.24/3.41  Reduction            : 0.75
% 9.24/3.41  Demodulation         : 0.51
% 9.24/3.41  BG Simplification    : 0.06
% 9.24/3.41  Subsumption          : 0.75
% 9.24/3.41  Abstraction          : 0.08
% 9.24/3.41  MUC search           : 0.00
% 9.24/3.41  Cooper               : 0.00
% 9.24/3.41  Total                : 2.67
% 9.24/3.41  Index Insertion      : 0.00
% 9.24/3.41  Index Deletion       : 0.00
% 9.24/3.41  Index Matching       : 0.00
% 9.24/3.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
