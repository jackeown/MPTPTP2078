%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:57 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 447 expanded)
%              Number of leaves         :   38 ( 167 expanded)
%              Depth                    :   17
%              Number of atoms          :  260 (1701 expanded)
%              Number of equality atoms :   30 (  87 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_14,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(A_57,k1_zfmisc_1(B_58))
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    ! [B_48] :
      ( ~ v1_subset_1(B_48,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_92,plain,(
    ! [B_58] :
      ( ~ v1_subset_1(B_58,B_58)
      | ~ r1_tarski(B_58,B_58) ) ),
    inference(resolution,[status(thm)],[c_85,c_46])).

tff(c_96,plain,(
    ! [B_58] : ~ v1_subset_1(B_58,B_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_92])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_80,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_80])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_206,plain,(
    ! [B_74,A_75] :
      ( v1_xboole_0(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_212,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_206])).

tff(c_216,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_212])).

tff(c_291,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_93)
      | r2_hidden('#skF_2'(A_92,B_93),A_92)
      | B_93 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_408,plain,(
    ! [A_112,B_113] :
      ( m1_subset_1('#skF_1'(A_112,B_113),B_113)
      | r2_hidden('#skF_2'(A_112,B_113),A_112)
      | B_113 = A_112 ) ),
    inference(resolution,[status(thm)],[c_291,c_18])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_246,plain,(
    ! [A_82,C_83,B_84] :
      ( m1_subset_1(A_82,C_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(C_83))
      | ~ r2_hidden(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_251,plain,(
    ! [A_82,B_14,A_13] :
      ( m1_subset_1(A_82,B_14)
      | ~ r2_hidden(A_82,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_246])).

tff(c_887,plain,(
    ! [A_151,B_152,B_153] :
      ( m1_subset_1('#skF_2'(A_151,B_152),B_153)
      | ~ r1_tarski(A_151,B_153)
      | m1_subset_1('#skF_1'(A_151,B_152),B_152)
      | B_152 = A_151 ) ),
    inference(resolution,[status(thm)],[c_408,c_251])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_362,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(A_104,B_105),B_105)
      | ~ r2_hidden('#skF_2'(A_104,B_105),B_105)
      | B_105 = A_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_552,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_1'(A_119,B_120),B_120)
      | B_120 = A_119
      | v1_xboole_0(B_120)
      | ~ m1_subset_1('#skF_2'(A_119,B_120),B_120) ) ),
    inference(resolution,[status(thm)],[c_20,c_362])).

tff(c_574,plain,(
    ! [A_119,B_120] :
      ( m1_subset_1('#skF_1'(A_119,B_120),B_120)
      | B_120 = A_119
      | v1_xboole_0(B_120)
      | ~ m1_subset_1('#skF_2'(A_119,B_120),B_120) ) ),
    inference(resolution,[status(thm)],[c_552,c_18])).

tff(c_928,plain,(
    ! [B_153,A_151] :
      ( v1_xboole_0(B_153)
      | ~ r1_tarski(A_151,B_153)
      | m1_subset_1('#skF_1'(A_151,B_153),B_153)
      | B_153 = A_151 ) ),
    inference(resolution,[status(thm)],[c_887,c_574])).

tff(c_50,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_68,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_98,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_121,plain,(
    ! [A_64,B_65] :
      ( r2_hidden(A_64,B_65)
      | v1_xboole_0(B_65)
      | ~ m1_subset_1(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_99,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_124,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_121,c_99])).

tff(c_130,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_124])).

tff(c_56,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_143,plain,(
    ! [B_68,A_69] :
      ( v1_subset_1(B_68,A_69)
      | B_68 = A_69
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_149,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_143])).

tff(c_153,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_149])).

tff(c_132,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_137,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_132])).

tff(c_142,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_154,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_142])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_154])).

tff(c_162,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_28,plain,(
    ! [A_18] :
      ( m1_subset_1(k3_yellow_0(A_18),u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_172,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_28])).

tff(c_176,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_172])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_176])).

tff(c_179,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_179])).

tff(c_182,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_252,plain,(
    ! [A_82] :
      ( m1_subset_1(A_82,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_82,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_246])).

tff(c_30,plain,(
    ! [A_19,B_21] :
      ( r1_orders_2(A_19,k3_yellow_0(A_19),B_21)
      | ~ m1_subset_1(B_21,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19)
      | ~ v1_yellow_0(A_19)
      | ~ v5_orders_2(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1692,plain,(
    ! [D_200,B_201,A_202,C_203] :
      ( r2_hidden(D_200,B_201)
      | ~ r1_orders_2(A_202,C_203,D_200)
      | ~ r2_hidden(C_203,B_201)
      | ~ m1_subset_1(D_200,u1_struct_0(A_202))
      | ~ m1_subset_1(C_203,u1_struct_0(A_202))
      | ~ v13_waybel_0(B_201,A_202)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_orders_2(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1996,plain,(
    ! [B_224,B_225,A_226] :
      ( r2_hidden(B_224,B_225)
      | ~ r2_hidden(k3_yellow_0(A_226),B_225)
      | ~ m1_subset_1(k3_yellow_0(A_226),u1_struct_0(A_226))
      | ~ v13_waybel_0(B_225,A_226)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ m1_subset_1(B_224,u1_struct_0(A_226))
      | ~ l1_orders_2(A_226)
      | ~ v1_yellow_0(A_226)
      | ~ v5_orders_2(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_30,c_1692])).

tff(c_2005,plain,(
    ! [B_224,B_225] :
      ( r2_hidden(B_224,B_225)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_225)
      | ~ v13_waybel_0(B_225,'#skF_5')
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_224,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_252,c_1996])).

tff(c_2018,plain,(
    ! [B_224,B_225] :
      ( r2_hidden(B_224,B_225)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_225)
      | ~ v13_waybel_0(B_225,'#skF_5')
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_224,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_60,c_58,c_56,c_2005])).

tff(c_2171,plain,(
    ! [B_241,B_242] :
      ( r2_hidden(B_241,B_242)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_242)
      | ~ v13_waybel_0(B_242,'#skF_5')
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_241,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2018])).

tff(c_2236,plain,(
    ! [B_241] :
      ( r2_hidden(B_241,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_241,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_2171])).

tff(c_2261,plain,(
    ! [B_243] :
      ( r2_hidden(B_243,'#skF_6')
      | ~ m1_subset_1(B_243,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_182,c_2236])).

tff(c_2305,plain,(
    ! [A_151] :
      ( r2_hidden('#skF_1'(A_151,u1_struct_0('#skF_5')),'#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_151,u1_struct_0('#skF_5'))
      | u1_struct_0('#skF_5') = A_151 ) ),
    inference(resolution,[status(thm)],[c_928,c_2261])).

tff(c_2660,plain,(
    ! [A_255] :
      ( r2_hidden('#skF_1'(A_255,u1_struct_0('#skF_5')),'#skF_6')
      | ~ r1_tarski(A_255,u1_struct_0('#skF_5'))
      | u1_struct_0('#skF_5') = A_255 ) ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_2305])).

tff(c_350,plain,(
    ! [A_102,B_103] :
      ( ~ r2_hidden('#skF_1'(A_102,B_103),A_102)
      | r2_hidden('#skF_2'(A_102,B_103),A_102)
      | B_103 = A_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_361,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1('#skF_2'(A_102,B_103),A_102)
      | ~ r2_hidden('#skF_1'(A_102,B_103),A_102)
      | B_103 = A_102 ) ),
    inference(resolution,[status(thm)],[c_350,c_18])).

tff(c_2667,plain,
    ( m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2660,c_361])).

tff(c_2681,plain,
    ( m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2667])).

tff(c_2687,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2681])).

tff(c_195,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_200,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_195])).

tff(c_205,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_2702,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2687,c_205])).

tff(c_2709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2702])).

tff(c_2710,plain,(
    m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2681])).

tff(c_254,plain,(
    ! [A_86,B_87,A_88] :
      ( m1_subset_1(A_86,B_87)
      | ~ r2_hidden(A_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(resolution,[status(thm)],[c_24,c_246])).

tff(c_306,plain,(
    ! [A_94,B_95,B_96] :
      ( m1_subset_1(A_94,B_95)
      | ~ r1_tarski(B_96,B_95)
      | v1_xboole_0(B_96)
      | ~ m1_subset_1(A_94,B_96) ) ),
    inference(resolution,[status(thm)],[c_20,c_254])).

tff(c_310,plain,(
    ! [A_94] :
      ( m1_subset_1(A_94,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_94,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_84,c_306])).

tff(c_316,plain,(
    ! [A_94] :
      ( m1_subset_1(A_94,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_94,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_310])).

tff(c_2711,plain,(
    u1_struct_0('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2681])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2670,plain,
    ( ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2660,c_2])).

tff(c_2684,plain,
    ( ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2670])).

tff(c_2777,plain,(
    ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2711,c_2684])).

tff(c_2780,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_2777])).

tff(c_2783,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_2780])).

tff(c_2790,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_316,c_2783])).

tff(c_2801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2710,c_2790])).

tff(c_2802,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_183,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2804,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2802,c_183])).

tff(c_2808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:11:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.95  
% 4.82/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/1.95  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 5.20/1.95  
% 5.20/1.95  %Foreground sorts:
% 5.20/1.95  
% 5.20/1.95  
% 5.20/1.95  %Background operators:
% 5.20/1.95  
% 5.20/1.95  
% 5.20/1.95  %Foreground operators:
% 5.20/1.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.20/1.95  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.20/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.20/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.20/1.95  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.20/1.95  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.20/1.95  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 5.20/1.95  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 5.20/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.20/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.20/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.20/1.95  tff('#skF_6', type, '#skF_6': $i).
% 5.20/1.95  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.20/1.95  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.20/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.20/1.95  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.20/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.20/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.20/1.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.20/1.95  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 5.20/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.20/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.20/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.20/1.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.20/1.95  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 5.20/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.20/1.95  
% 5.20/1.97  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.20/1.97  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.20/1.97  tff(f_109, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 5.20/1.97  tff(f_138, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 5.20/1.97  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.20/1.97  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.20/1.97  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.20/1.97  tff(f_65, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.20/1.97  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.20/1.97  tff(f_69, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 5.20/1.97  tff(f_83, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 5.20/1.97  tff(f_102, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 5.20/1.97  tff(c_14, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.20/1.97  tff(c_85, plain, (![A_57, B_58]: (m1_subset_1(A_57, k1_zfmisc_1(B_58)) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.20/1.97  tff(c_46, plain, (![B_48]: (~v1_subset_1(B_48, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.20/1.97  tff(c_92, plain, (![B_58]: (~v1_subset_1(B_58, B_58) | ~r1_tarski(B_58, B_58))), inference(resolution, [status(thm)], [c_85, c_46])).
% 5.20/1.97  tff(c_96, plain, (![B_58]: (~v1_subset_1(B_58, B_58))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_92])).
% 5.20/1.97  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.20/1.97  tff(c_80, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.20/1.97  tff(c_84, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_80])).
% 5.20/1.97  tff(c_54, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.20/1.97  tff(c_206, plain, (![B_74, A_75]: (v1_xboole_0(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.20/1.97  tff(c_212, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_206])).
% 5.20/1.97  tff(c_216, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_212])).
% 5.20/1.97  tff(c_291, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92, B_93), B_93) | r2_hidden('#skF_2'(A_92, B_93), A_92) | B_93=A_92)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.20/1.97  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.20/1.97  tff(c_408, plain, (![A_112, B_113]: (m1_subset_1('#skF_1'(A_112, B_113), B_113) | r2_hidden('#skF_2'(A_112, B_113), A_112) | B_113=A_112)), inference(resolution, [status(thm)], [c_291, c_18])).
% 5.20/1.97  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.20/1.97  tff(c_246, plain, (![A_82, C_83, B_84]: (m1_subset_1(A_82, C_83) | ~m1_subset_1(B_84, k1_zfmisc_1(C_83)) | ~r2_hidden(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.20/1.97  tff(c_251, plain, (![A_82, B_14, A_13]: (m1_subset_1(A_82, B_14) | ~r2_hidden(A_82, A_13) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_24, c_246])).
% 5.20/1.97  tff(c_887, plain, (![A_151, B_152, B_153]: (m1_subset_1('#skF_2'(A_151, B_152), B_153) | ~r1_tarski(A_151, B_153) | m1_subset_1('#skF_1'(A_151, B_152), B_152) | B_152=A_151)), inference(resolution, [status(thm)], [c_408, c_251])).
% 5.20/1.97  tff(c_20, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.20/1.97  tff(c_362, plain, (![A_104, B_105]: (r2_hidden('#skF_1'(A_104, B_105), B_105) | ~r2_hidden('#skF_2'(A_104, B_105), B_105) | B_105=A_104)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.20/1.97  tff(c_552, plain, (![A_119, B_120]: (r2_hidden('#skF_1'(A_119, B_120), B_120) | B_120=A_119 | v1_xboole_0(B_120) | ~m1_subset_1('#skF_2'(A_119, B_120), B_120))), inference(resolution, [status(thm)], [c_20, c_362])).
% 5.20/1.97  tff(c_574, plain, (![A_119, B_120]: (m1_subset_1('#skF_1'(A_119, B_120), B_120) | B_120=A_119 | v1_xboole_0(B_120) | ~m1_subset_1('#skF_2'(A_119, B_120), B_120))), inference(resolution, [status(thm)], [c_552, c_18])).
% 5.20/1.97  tff(c_928, plain, (![B_153, A_151]: (v1_xboole_0(B_153) | ~r1_tarski(A_151, B_153) | m1_subset_1('#skF_1'(A_151, B_153), B_153) | B_153=A_151)), inference(resolution, [status(thm)], [c_887, c_574])).
% 5.20/1.97  tff(c_50, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.20/1.97  tff(c_68, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.20/1.97  tff(c_98, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_68])).
% 5.20/1.97  tff(c_121, plain, (![A_64, B_65]: (r2_hidden(A_64, B_65) | v1_xboole_0(B_65) | ~m1_subset_1(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.20/1.97  tff(c_74, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.20/1.97  tff(c_99, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_74])).
% 5.20/1.97  tff(c_124, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_121, c_99])).
% 5.20/1.97  tff(c_130, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_124])).
% 5.20/1.97  tff(c_56, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.20/1.97  tff(c_143, plain, (![B_68, A_69]: (v1_subset_1(B_68, A_69) | B_68=A_69 | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.20/1.97  tff(c_149, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_48, c_143])).
% 5.20/1.97  tff(c_153, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_98, c_149])).
% 5.20/1.97  tff(c_132, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.20/1.97  tff(c_137, plain, (u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_84, c_132])).
% 5.20/1.97  tff(c_142, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_137])).
% 5.20/1.97  tff(c_154, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_142])).
% 5.20/1.97  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_154])).
% 5.20/1.97  tff(c_162, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_137])).
% 5.20/1.97  tff(c_28, plain, (![A_18]: (m1_subset_1(k3_yellow_0(A_18), u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.20/1.97  tff(c_172, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_162, c_28])).
% 5.20/1.97  tff(c_176, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_172])).
% 5.20/1.97  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_176])).
% 5.20/1.97  tff(c_179, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 5.20/1.97  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_179])).
% 5.20/1.97  tff(c_182, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 5.20/1.97  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.20/1.97  tff(c_60, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.20/1.97  tff(c_58, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.20/1.97  tff(c_252, plain, (![A_82]: (m1_subset_1(A_82, u1_struct_0('#skF_5')) | ~r2_hidden(A_82, '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_246])).
% 5.20/1.97  tff(c_30, plain, (![A_19, B_21]: (r1_orders_2(A_19, k3_yellow_0(A_19), B_21) | ~m1_subset_1(B_21, u1_struct_0(A_19)) | ~l1_orders_2(A_19) | ~v1_yellow_0(A_19) | ~v5_orders_2(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.20/1.97  tff(c_1692, plain, (![D_200, B_201, A_202, C_203]: (r2_hidden(D_200, B_201) | ~r1_orders_2(A_202, C_203, D_200) | ~r2_hidden(C_203, B_201) | ~m1_subset_1(D_200, u1_struct_0(A_202)) | ~m1_subset_1(C_203, u1_struct_0(A_202)) | ~v13_waybel_0(B_201, A_202) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_orders_2(A_202))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.20/1.97  tff(c_1996, plain, (![B_224, B_225, A_226]: (r2_hidden(B_224, B_225) | ~r2_hidden(k3_yellow_0(A_226), B_225) | ~m1_subset_1(k3_yellow_0(A_226), u1_struct_0(A_226)) | ~v13_waybel_0(B_225, A_226) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_226))) | ~m1_subset_1(B_224, u1_struct_0(A_226)) | ~l1_orders_2(A_226) | ~v1_yellow_0(A_226) | ~v5_orders_2(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_30, c_1692])).
% 5.20/1.97  tff(c_2005, plain, (![B_224, B_225]: (r2_hidden(B_224, B_225) | ~r2_hidden(k3_yellow_0('#skF_5'), B_225) | ~v13_waybel_0(B_225, '#skF_5') | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_224, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_252, c_1996])).
% 5.20/1.97  tff(c_2018, plain, (![B_224, B_225]: (r2_hidden(B_224, B_225) | ~r2_hidden(k3_yellow_0('#skF_5'), B_225) | ~v13_waybel_0(B_225, '#skF_5') | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_224, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_60, c_58, c_56, c_2005])).
% 5.20/1.97  tff(c_2171, plain, (![B_241, B_242]: (r2_hidden(B_241, B_242) | ~r2_hidden(k3_yellow_0('#skF_5'), B_242) | ~v13_waybel_0(B_242, '#skF_5') | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_241, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_2018])).
% 5.20/1.97  tff(c_2236, plain, (![B_241]: (r2_hidden(B_241, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_241, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_48, c_2171])).
% 5.20/1.97  tff(c_2261, plain, (![B_243]: (r2_hidden(B_243, '#skF_6') | ~m1_subset_1(B_243, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_182, c_2236])).
% 5.20/1.97  tff(c_2305, plain, (![A_151]: (r2_hidden('#skF_1'(A_151, u1_struct_0('#skF_5')), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')) | ~r1_tarski(A_151, u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')=A_151)), inference(resolution, [status(thm)], [c_928, c_2261])).
% 5.20/1.97  tff(c_2660, plain, (![A_255]: (r2_hidden('#skF_1'(A_255, u1_struct_0('#skF_5')), '#skF_6') | ~r1_tarski(A_255, u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')=A_255)), inference(negUnitSimplification, [status(thm)], [c_216, c_2305])).
% 5.20/1.97  tff(c_350, plain, (![A_102, B_103]: (~r2_hidden('#skF_1'(A_102, B_103), A_102) | r2_hidden('#skF_2'(A_102, B_103), A_102) | B_103=A_102)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.20/1.97  tff(c_361, plain, (![A_102, B_103]: (m1_subset_1('#skF_2'(A_102, B_103), A_102) | ~r2_hidden('#skF_1'(A_102, B_103), A_102) | B_103=A_102)), inference(resolution, [status(thm)], [c_350, c_18])).
% 5.20/1.97  tff(c_2667, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~r1_tarski('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_2660, c_361])).
% 5.20/1.97  tff(c_2681, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2667])).
% 5.20/1.97  tff(c_2687, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_2681])).
% 5.20/1.97  tff(c_195, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.20/1.97  tff(c_200, plain, (u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_84, c_195])).
% 5.20/1.97  tff(c_205, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_200])).
% 5.20/1.97  tff(c_2702, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2687, c_205])).
% 5.20/1.97  tff(c_2709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_2702])).
% 5.20/1.97  tff(c_2710, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_2681])).
% 5.20/1.97  tff(c_254, plain, (![A_86, B_87, A_88]: (m1_subset_1(A_86, B_87) | ~r2_hidden(A_86, A_88) | ~r1_tarski(A_88, B_87))), inference(resolution, [status(thm)], [c_24, c_246])).
% 5.20/1.97  tff(c_306, plain, (![A_94, B_95, B_96]: (m1_subset_1(A_94, B_95) | ~r1_tarski(B_96, B_95) | v1_xboole_0(B_96) | ~m1_subset_1(A_94, B_96))), inference(resolution, [status(thm)], [c_20, c_254])).
% 5.20/1.97  tff(c_310, plain, (![A_94]: (m1_subset_1(A_94, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_94, '#skF_6'))), inference(resolution, [status(thm)], [c_84, c_306])).
% 5.20/1.97  tff(c_316, plain, (![A_94]: (m1_subset_1(A_94, u1_struct_0('#skF_5')) | ~m1_subset_1(A_94, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_310])).
% 5.20/1.97  tff(c_2711, plain, (u1_struct_0('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_2681])).
% 5.20/1.97  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.20/1.97  tff(c_2670, plain, (~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~r1_tarski('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_2660, c_2])).
% 5.20/1.97  tff(c_2684, plain, (~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2670])).
% 5.20/1.97  tff(c_2777, plain, (~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2711, c_2684])).
% 5.20/1.97  tff(c_2780, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_2777])).
% 5.20/1.97  tff(c_2783, plain, (~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_216, c_2780])).
% 5.20/1.97  tff(c_2790, plain, (~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(resolution, [status(thm)], [c_316, c_2783])).
% 5.20/1.97  tff(c_2801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2710, c_2790])).
% 5.20/1.97  tff(c_2802, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_200])).
% 5.20/1.97  tff(c_183, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_68])).
% 5.20/1.97  tff(c_2804, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2802, c_183])).
% 5.20/1.97  tff(c_2808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_2804])).
% 5.20/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/1.97  
% 5.20/1.97  Inference rules
% 5.20/1.97  ----------------------
% 5.20/1.97  #Ref     : 0
% 5.20/1.97  #Sup     : 560
% 5.20/1.97  #Fact    : 0
% 5.20/1.97  #Define  : 0
% 5.20/1.97  #Split   : 9
% 5.20/1.97  #Chain   : 0
% 5.20/1.97  #Close   : 0
% 5.20/1.97  
% 5.20/1.97  Ordering : KBO
% 5.20/1.97  
% 5.20/1.97  Simplification rules
% 5.20/1.97  ----------------------
% 5.20/1.97  #Subsume      : 57
% 5.20/1.97  #Demod        : 103
% 5.20/1.97  #Tautology    : 104
% 5.20/1.97  #SimpNegUnit  : 51
% 5.20/1.97  #BackRed      : 29
% 5.20/1.97  
% 5.20/1.97  #Partial instantiations: 0
% 5.20/1.97  #Strategies tried      : 1
% 5.20/1.97  
% 5.20/1.97  Timing (in seconds)
% 5.20/1.97  ----------------------
% 5.20/1.98  Preprocessing        : 0.34
% 5.20/1.98  Parsing              : 0.19
% 5.20/1.98  CNF conversion       : 0.03
% 5.20/1.98  Main loop            : 0.83
% 5.20/1.98  Inferencing          : 0.28
% 5.20/1.98  Reduction            : 0.21
% 5.20/1.98  Demodulation         : 0.13
% 5.20/1.98  BG Simplification    : 0.04
% 5.20/1.98  Subsumption          : 0.23
% 5.20/1.98  Abstraction          : 0.04
% 5.20/1.98  MUC search           : 0.00
% 5.20/1.98  Cooper               : 0.00
% 5.20/1.98  Total                : 1.21
% 5.20/1.98  Index Insertion      : 0.00
% 5.20/1.98  Index Deletion       : 0.00
% 5.20/1.98  Index Matching       : 0.00
% 5.20/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
