%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:59 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.45s
% Verified   : 
% Statistics : Number of formulae       :  196 (1230 expanded)
%              Number of leaves         :   38 ( 419 expanded)
%              Depth                    :   21
%              Number of atoms          :  447 (4571 expanded)
%              Number of equality atoms :   48 ( 182 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_14,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(A_58,k1_zfmisc_1(B_59))
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    ! [B_49] :
      ( ~ v1_subset_1(B_49,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_92,plain,(
    ! [B_59] :
      ( ~ v1_subset_1(B_59,B_59)
      | ~ r1_tarski(B_59,B_59) ) ),
    inference(resolution,[status(thm)],[c_85,c_46])).

tff(c_96,plain,(
    ! [B_59] : ~ v1_subset_1(B_59,B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_92])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_80,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_80])).

tff(c_291,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_93)
      | r2_hidden('#skF_2'(A_92,B_93),A_92)
      | B_93 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_661,plain,(
    ! [A_134,B_135] :
      ( m1_subset_1('#skF_2'(A_134,B_135),A_134)
      | r2_hidden('#skF_1'(A_134,B_135),B_135)
      | B_135 = A_134 ) ),
    inference(resolution,[status(thm)],[c_291,c_18])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_210,plain,(
    ! [A_75,C_76,B_77] :
      ( m1_subset_1(A_75,C_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(C_76))
      | ~ r2_hidden(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_215,plain,(
    ! [A_75,B_15,A_14] :
      ( m1_subset_1(A_75,B_15)
      | ~ r2_hidden(A_75,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_210])).

tff(c_2327,plain,(
    ! [A_256,B_257,B_258] :
      ( m1_subset_1('#skF_1'(A_256,B_257),B_258)
      | ~ r1_tarski(B_257,B_258)
      | m1_subset_1('#skF_2'(A_256,B_257),A_256)
      | B_257 = A_256 ) ),
    inference(resolution,[status(thm)],[c_661,c_215])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_253,plain,(
    ! [C_86,A_87,B_88] :
      ( r2_hidden(C_86,A_87)
      | ~ r2_hidden(C_86,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_712,plain,(
    ! [A_136,A_137,B_138] :
      ( r2_hidden(A_136,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137))
      | v1_xboole_0(B_138)
      | ~ m1_subset_1(A_136,B_138) ) ),
    inference(resolution,[status(thm)],[c_20,c_253])).

tff(c_730,plain,(
    ! [A_136] :
      ( r2_hidden(A_136,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_136,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_712])).

tff(c_741,plain,(
    ! [A_136] :
      ( r2_hidden(A_136,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_136,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_730])).

tff(c_68,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_98,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_56,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_122,plain,(
    ! [B_65,A_66] :
      ( v1_subset_1(B_65,A_66)
      | B_65 = A_66
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_128,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_122])).

tff(c_132,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_128])).

tff(c_100,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_105,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_100])).

tff(c_110,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_133,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_110])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_133])).

tff(c_140,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_28,plain,(
    ! [A_19] :
      ( m1_subset_1(k3_yellow_0(A_19),u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_149,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_28])).

tff(c_153,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_149])).

tff(c_161,plain,(
    ! [A_67,B_68] :
      ( r2_hidden(A_67,B_68)
      | v1_xboole_0(B_68)
      | ~ m1_subset_1(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_99,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_164,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_161,c_99])).

tff(c_170,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_164])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_170])).

tff(c_173,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_173])).

tff(c_176,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_260,plain,(
    ! [A_89] :
      ( r2_hidden(k3_yellow_0('#skF_5'),A_89)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_176,c_253])).

tff(c_325,plain,(
    ! [B_98,A_99] :
      ( m1_subset_1(k3_yellow_0('#skF_5'),B_98)
      | ~ r1_tarski(A_99,B_98)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_99)) ) ),
    inference(resolution,[status(thm)],[c_260,c_215])).

tff(c_333,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_325])).

tff(c_335,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_338,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_335])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_338])).

tff(c_344,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_720,plain,(
    ! [A_136] :
      ( r2_hidden(A_136,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_136,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_344,c_712])).

tff(c_742,plain,(
    ! [A_139] :
      ( r2_hidden(A_139,'#skF_6')
      | ~ m1_subset_1(A_139,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_720])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1080,plain,(
    ! [B_169] :
      ( ~ r2_hidden('#skF_2'('#skF_6',B_169),B_169)
      | B_169 = '#skF_6'
      | ~ m1_subset_1('#skF_1'('#skF_6',B_169),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_742,c_2])).

tff(c_1115,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_741,c_1080])).

tff(c_2075,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1115])).

tff(c_2427,plain,(
    ! [B_258] :
      ( m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),B_258)
      | ~ r1_tarski(u1_struct_0('#skF_5'),B_258)
      | u1_struct_0('#skF_5') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_2327,c_2075])).

tff(c_2514,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2427])).

tff(c_216,plain,(
    ! [A_75] :
      ( m1_subset_1(A_75,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_75,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_210])).

tff(c_858,plain,(
    ! [A_151,B_152,A_153] :
      ( r2_hidden(A_151,B_152)
      | v1_xboole_0(A_153)
      | ~ m1_subset_1(A_151,A_153)
      | ~ r1_tarski(A_153,B_152) ) ),
    inference(resolution,[status(thm)],[c_24,c_712])).

tff(c_893,plain,(
    ! [A_75,B_152] :
      ( r2_hidden(A_75,B_152)
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r1_tarski(u1_struct_0('#skF_5'),B_152)
      | ~ r2_hidden(A_75,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_216,c_858])).

tff(c_1181,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_893])).

tff(c_2521,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2514,c_1181])).

tff(c_2541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2521])).

tff(c_2543,plain,(
    u1_struct_0('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2427])).

tff(c_2542,plain,(
    ! [B_258] :
      ( m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),B_258)
      | ~ r1_tarski(u1_struct_0('#skF_5'),B_258) ) ),
    inference(splitRight,[status(thm)],[c_2427])).

tff(c_50,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_30,plain,(
    ! [A_20,B_22] :
      ( r1_orders_2(A_20,k3_yellow_0(A_20),B_22)
      | ~ m1_subset_1(B_22,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20)
      | ~ v1_yellow_0(A_20)
      | ~ v5_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1314,plain,(
    ! [D_196,B_197,A_198,C_199] :
      ( r2_hidden(D_196,B_197)
      | ~ r1_orders_2(A_198,C_199,D_196)
      | ~ r2_hidden(C_199,B_197)
      | ~ m1_subset_1(D_196,u1_struct_0(A_198))
      | ~ m1_subset_1(C_199,u1_struct_0(A_198))
      | ~ v13_waybel_0(B_197,A_198)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_orders_2(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2632,plain,(
    ! [B_263,B_264,A_265] :
      ( r2_hidden(B_263,B_264)
      | ~ r2_hidden(k3_yellow_0(A_265),B_264)
      | ~ m1_subset_1(k3_yellow_0(A_265),u1_struct_0(A_265))
      | ~ v13_waybel_0(B_264,A_265)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ m1_subset_1(B_263,u1_struct_0(A_265))
      | ~ l1_orders_2(A_265)
      | ~ v1_yellow_0(A_265)
      | ~ v5_orders_2(A_265)
      | v2_struct_0(A_265) ) ),
    inference(resolution,[status(thm)],[c_30,c_1314])).

tff(c_2646,plain,(
    ! [B_263,B_264] :
      ( r2_hidden(B_263,B_264)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_264)
      | ~ v13_waybel_0(B_264,'#skF_5')
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_263,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_216,c_2632])).

tff(c_2667,plain,(
    ! [B_263,B_264] :
      ( r2_hidden(B_263,B_264)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_264)
      | ~ v13_waybel_0(B_264,'#skF_5')
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_263,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_60,c_58,c_56,c_2646])).

tff(c_2966,plain,(
    ! [B_274,B_275] :
      ( r2_hidden(B_274,B_275)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_275)
      | ~ v13_waybel_0(B_275,'#skF_5')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_274,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2667])).

tff(c_3022,plain,(
    ! [B_274] :
      ( r2_hidden(B_274,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_274,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_2966])).

tff(c_3045,plain,(
    ! [B_276] :
      ( r2_hidden(B_276,'#skF_6')
      | ~ m1_subset_1(B_276,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_176,c_3022])).

tff(c_3061,plain,
    ( r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2542,c_3045])).

tff(c_3144,plain,(
    r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3061])).

tff(c_413,plain,(
    ! [A_108,B_109] :
      ( ~ r2_hidden('#skF_1'(A_108,B_109),A_108)
      | r2_hidden('#skF_2'(A_108,B_109),A_108)
      | B_109 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_433,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1('#skF_2'(A_108,B_109),A_108)
      | ~ r2_hidden('#skF_1'(A_108,B_109),A_108)
      | B_109 = A_108 ) ),
    inference(resolution,[status(thm)],[c_413,c_18])).

tff(c_3187,plain,
    ( m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3144,c_433])).

tff(c_3206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2543,c_2075,c_3187])).

tff(c_3207,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1115])).

tff(c_3214,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3207])).

tff(c_3208,plain,(
    m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1115])).

tff(c_738,plain,(
    ! [A_136,B_15,A_14] :
      ( r2_hidden(A_136,B_15)
      | v1_xboole_0(A_14)
      | ~ m1_subset_1(A_136,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_712])).

tff(c_3210,plain,(
    ! [B_15] :
      ( r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),B_15)
      | v1_xboole_0('#skF_6')
      | ~ r1_tarski('#skF_6',B_15) ) ),
    inference(resolution,[status(thm)],[c_3208,c_738])).

tff(c_3274,plain,(
    ! [B_279] :
      ( r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),B_279)
      | ~ r1_tarski('#skF_6',B_279) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3210])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3288,plain,
    ( r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3274,c_4])).

tff(c_3309,plain,
    ( r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3288])).

tff(c_3374,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3309])).

tff(c_3399,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3374,c_1181])).

tff(c_3419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3399])).

tff(c_3420,plain,(
    r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3309])).

tff(c_3430,plain,(
    ! [B_15] :
      ( m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),B_15)
      | ~ r1_tarski(u1_struct_0('#skF_5'),B_15) ) ),
    inference(resolution,[status(thm)],[c_3420,c_215])).

tff(c_3466,plain,(
    ! [B_284,B_285,A_286] :
      ( r2_hidden(B_284,B_285)
      | ~ r2_hidden(k3_yellow_0(A_286),B_285)
      | ~ m1_subset_1(k3_yellow_0(A_286),u1_struct_0(A_286))
      | ~ v13_waybel_0(B_285,A_286)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ m1_subset_1(B_284,u1_struct_0(A_286))
      | ~ l1_orders_2(A_286)
      | ~ v1_yellow_0(A_286)
      | ~ v5_orders_2(A_286)
      | v2_struct_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_30,c_1314])).

tff(c_3480,plain,(
    ! [B_284,B_285] :
      ( r2_hidden(B_284,B_285)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_285)
      | ~ v13_waybel_0(B_285,'#skF_5')
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_284,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_216,c_3466])).

tff(c_3501,plain,(
    ! [B_284,B_285] :
      ( r2_hidden(B_284,B_285)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_285)
      | ~ v13_waybel_0(B_285,'#skF_5')
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_284,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_60,c_58,c_56,c_3480])).

tff(c_3630,plain,(
    ! [B_290,B_291] :
      ( r2_hidden(B_290,B_291)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_291)
      | ~ v13_waybel_0(B_291,'#skF_5')
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_290,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3501])).

tff(c_3671,plain,(
    ! [B_290] :
      ( r2_hidden(B_290,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_290,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_3630])).

tff(c_3689,plain,(
    ! [B_292] :
      ( r2_hidden(B_292,'#skF_6')
      | ~ m1_subset_1(B_292,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_176,c_3671])).

tff(c_3693,plain,
    ( r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3430,c_3689])).

tff(c_3768,plain,(
    r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3693])).

tff(c_3828,plain,(
    m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3768,c_18])).

tff(c_3843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3214,c_3828])).

tff(c_3844,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3207])).

tff(c_3851,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3844,c_1181])).

tff(c_3871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3851])).

tff(c_3873,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_893])).

tff(c_614,plain,(
    ! [A_132,B_133] :
      ( m1_subset_1('#skF_1'(A_132,B_133),B_133)
      | r2_hidden('#skF_2'(A_132,B_133),A_132)
      | B_133 = A_132 ) ),
    inference(resolution,[status(thm)],[c_291,c_18])).

tff(c_4834,plain,(
    ! [A_371,B_372,B_373] :
      ( m1_subset_1('#skF_2'(A_371,B_372),B_373)
      | ~ r1_tarski(A_371,B_373)
      | m1_subset_1('#skF_1'(A_371,B_372),B_372)
      | B_372 = A_371 ) ),
    inference(resolution,[status(thm)],[c_614,c_215])).

tff(c_384,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_1'(A_103,B_104),B_104)
      | ~ r2_hidden('#skF_2'(A_103,B_104),B_104)
      | B_104 = A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4134,plain,(
    ! [A_332,B_333] :
      ( r2_hidden('#skF_1'(A_332,B_333),B_333)
      | B_333 = A_332
      | v1_xboole_0(B_333)
      | ~ m1_subset_1('#skF_2'(A_332,B_333),B_333) ) ),
    inference(resolution,[status(thm)],[c_20,c_384])).

tff(c_4163,plain,(
    ! [A_332,B_333] :
      ( m1_subset_1('#skF_1'(A_332,B_333),B_333)
      | B_333 = A_332
      | v1_xboole_0(B_333)
      | ~ m1_subset_1('#skF_2'(A_332,B_333),B_333) ) ),
    inference(resolution,[status(thm)],[c_4134,c_18])).

tff(c_4916,plain,(
    ! [B_373,A_371] :
      ( v1_xboole_0(B_373)
      | ~ r1_tarski(A_371,B_373)
      | m1_subset_1('#skF_1'(A_371,B_373),B_373)
      | B_373 = A_371 ) ),
    inference(resolution,[status(thm)],[c_4834,c_4163])).

tff(c_3966,plain,(
    ! [D_312,B_313,A_314,C_315] :
      ( r2_hidden(D_312,B_313)
      | ~ r1_orders_2(A_314,C_315,D_312)
      | ~ r2_hidden(C_315,B_313)
      | ~ m1_subset_1(D_312,u1_struct_0(A_314))
      | ~ m1_subset_1(C_315,u1_struct_0(A_314))
      | ~ v13_waybel_0(B_313,A_314)
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0(A_314)))
      | ~ l1_orders_2(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5847,plain,(
    ! [B_407,B_408,A_409] :
      ( r2_hidden(B_407,B_408)
      | ~ r2_hidden(k3_yellow_0(A_409),B_408)
      | ~ m1_subset_1(k3_yellow_0(A_409),u1_struct_0(A_409))
      | ~ v13_waybel_0(B_408,A_409)
      | ~ m1_subset_1(B_408,k1_zfmisc_1(u1_struct_0(A_409)))
      | ~ m1_subset_1(B_407,u1_struct_0(A_409))
      | ~ l1_orders_2(A_409)
      | ~ v1_yellow_0(A_409)
      | ~ v5_orders_2(A_409)
      | v2_struct_0(A_409) ) ),
    inference(resolution,[status(thm)],[c_30,c_3966])).

tff(c_5861,plain,(
    ! [B_407,B_408] :
      ( r2_hidden(B_407,B_408)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_408)
      | ~ v13_waybel_0(B_408,'#skF_5')
      | ~ m1_subset_1(B_408,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_407,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_216,c_5847])).

tff(c_5882,plain,(
    ! [B_407,B_408] :
      ( r2_hidden(B_407,B_408)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_408)
      | ~ v13_waybel_0(B_408,'#skF_5')
      | ~ m1_subset_1(B_408,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_407,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_60,c_58,c_56,c_5861])).

tff(c_5940,plain,(
    ! [B_413,B_414] :
      ( r2_hidden(B_413,B_414)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_414)
      | ~ v13_waybel_0(B_414,'#skF_5')
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_413,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5882])).

tff(c_6008,plain,(
    ! [B_413] :
      ( r2_hidden(B_413,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_413,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_5940])).

tff(c_6036,plain,(
    ! [B_415] :
      ( r2_hidden(B_415,'#skF_6')
      | ~ m1_subset_1(B_415,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_176,c_6008])).

tff(c_6072,plain,(
    ! [A_371] :
      ( r2_hidden('#skF_1'(A_371,u1_struct_0('#skF_5')),'#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_371,u1_struct_0('#skF_5'))
      | u1_struct_0('#skF_5') = A_371 ) ),
    inference(resolution,[status(thm)],[c_4916,c_6036])).

tff(c_6293,plain,(
    ! [A_421] :
      ( r2_hidden('#skF_1'(A_421,u1_struct_0('#skF_5')),'#skF_6')
      | ~ r1_tarski(A_421,u1_struct_0('#skF_5'))
      | u1_struct_0('#skF_5') = A_421 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3873,c_6072])).

tff(c_6303,plain,
    ( m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6293,c_433])).

tff(c_6322,plain,
    ( m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6303])).

tff(c_6329,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6322])).

tff(c_184,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_189,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_184])).

tff(c_194,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_6357,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6329,c_194])).

tff(c_6367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6357])).

tff(c_6369,plain,(
    u1_struct_0('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6322])).

tff(c_6368,plain,(
    m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_6322])).

tff(c_6371,plain,(
    ! [B_15] :
      ( r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),B_15)
      | v1_xboole_0('#skF_6')
      | ~ r1_tarski('#skF_6',B_15) ) ),
    inference(resolution,[status(thm)],[c_6368,c_738])).

tff(c_6375,plain,(
    ! [B_422] :
      ( r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),B_422)
      | ~ r1_tarski('#skF_6',B_422) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_6371])).

tff(c_407,plain,(
    ! [A_106,B_107] :
      ( ~ r2_hidden('#skF_1'(A_106,B_107),A_106)
      | ~ r2_hidden('#skF_2'(A_106,B_107),B_107)
      | B_107 = A_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_412,plain,(
    ! [B_13,B_107] :
      ( ~ r2_hidden('#skF_2'(B_13,B_107),B_107)
      | B_13 = B_107
      | v1_xboole_0(B_13)
      | ~ m1_subset_1('#skF_1'(B_13,B_107),B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_407])).

tff(c_6378,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | v1_xboole_0('#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6375,c_412])).

tff(c_6402,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | v1_xboole_0('#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6378])).

tff(c_6403,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_6369,c_6402])).

tff(c_6389,plain,
    ( r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6375,c_4])).

tff(c_6411,plain,
    ( r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6389])).

tff(c_6412,plain,(
    r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_6369,c_6411])).

tff(c_6546,plain,(
    m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6412,c_18])).

tff(c_6035,plain,(
    ! [B_413] :
      ( r2_hidden(B_413,'#skF_6')
      | ~ m1_subset_1(B_413,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_176,c_6008])).

tff(c_6552,plain,(
    r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_6546,c_6035])).

tff(c_6571,plain,(
    m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_6552,c_18])).

tff(c_6589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6403,c_6571])).

tff(c_6590,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_177,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6592,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6590,c_177])).

tff(c_6596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_6592])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:38:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.45/2.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.55  
% 7.45/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.55  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 7.45/2.55  
% 7.45/2.55  %Foreground sorts:
% 7.45/2.55  
% 7.45/2.55  
% 7.45/2.55  %Background operators:
% 7.45/2.55  
% 7.45/2.55  
% 7.45/2.55  %Foreground operators:
% 7.45/2.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.45/2.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.45/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.45/2.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.45/2.55  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.45/2.55  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.45/2.55  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 7.45/2.55  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 7.45/2.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.45/2.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.45/2.55  tff('#skF_5', type, '#skF_5': $i).
% 7.45/2.55  tff('#skF_6', type, '#skF_6': $i).
% 7.45/2.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.45/2.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.45/2.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.45/2.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.45/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.45/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.45/2.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.45/2.55  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 7.45/2.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.45/2.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.45/2.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.45/2.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.45/2.55  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 7.45/2.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.45/2.55  
% 7.45/2.58  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.45/2.58  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.45/2.58  tff(f_109, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 7.45/2.58  tff(f_138, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 7.45/2.58  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 7.45/2.58  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.45/2.58  tff(f_65, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.45/2.58  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.45/2.58  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.45/2.58  tff(f_69, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 7.45/2.58  tff(f_83, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 7.45/2.58  tff(f_102, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 7.45/2.58  tff(c_14, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.45/2.58  tff(c_85, plain, (![A_58, B_59]: (m1_subset_1(A_58, k1_zfmisc_1(B_59)) | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.45/2.58  tff(c_46, plain, (![B_49]: (~v1_subset_1(B_49, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.45/2.58  tff(c_92, plain, (![B_59]: (~v1_subset_1(B_59, B_59) | ~r1_tarski(B_59, B_59))), inference(resolution, [status(thm)], [c_85, c_46])).
% 7.45/2.58  tff(c_96, plain, (![B_59]: (~v1_subset_1(B_59, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_92])).
% 7.45/2.58  tff(c_54, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.45/2.58  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.45/2.58  tff(c_80, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.45/2.58  tff(c_84, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_80])).
% 7.45/2.58  tff(c_291, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92, B_93), B_93) | r2_hidden('#skF_2'(A_92, B_93), A_92) | B_93=A_92)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.45/2.58  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.45/2.58  tff(c_661, plain, (![A_134, B_135]: (m1_subset_1('#skF_2'(A_134, B_135), A_134) | r2_hidden('#skF_1'(A_134, B_135), B_135) | B_135=A_134)), inference(resolution, [status(thm)], [c_291, c_18])).
% 7.45/2.58  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.45/2.58  tff(c_210, plain, (![A_75, C_76, B_77]: (m1_subset_1(A_75, C_76) | ~m1_subset_1(B_77, k1_zfmisc_1(C_76)) | ~r2_hidden(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.45/2.58  tff(c_215, plain, (![A_75, B_15, A_14]: (m1_subset_1(A_75, B_15) | ~r2_hidden(A_75, A_14) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_24, c_210])).
% 7.45/2.58  tff(c_2327, plain, (![A_256, B_257, B_258]: (m1_subset_1('#skF_1'(A_256, B_257), B_258) | ~r1_tarski(B_257, B_258) | m1_subset_1('#skF_2'(A_256, B_257), A_256) | B_257=A_256)), inference(resolution, [status(thm)], [c_661, c_215])).
% 7.45/2.58  tff(c_20, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.45/2.58  tff(c_253, plain, (![C_86, A_87, B_88]: (r2_hidden(C_86, A_87) | ~r2_hidden(C_86, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.45/2.58  tff(c_712, plain, (![A_136, A_137, B_138]: (r2_hidden(A_136, A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)) | v1_xboole_0(B_138) | ~m1_subset_1(A_136, B_138))), inference(resolution, [status(thm)], [c_20, c_253])).
% 7.45/2.58  tff(c_730, plain, (![A_136]: (r2_hidden(A_136, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_136, '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_712])).
% 7.45/2.58  tff(c_741, plain, (![A_136]: (r2_hidden(A_136, u1_struct_0('#skF_5')) | ~m1_subset_1(A_136, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_730])).
% 7.45/2.58  tff(c_68, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.45/2.58  tff(c_98, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_68])).
% 7.45/2.58  tff(c_56, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.45/2.58  tff(c_122, plain, (![B_65, A_66]: (v1_subset_1(B_65, A_66) | B_65=A_66 | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.45/2.58  tff(c_128, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_48, c_122])).
% 7.45/2.58  tff(c_132, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_98, c_128])).
% 7.45/2.58  tff(c_100, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.45/2.58  tff(c_105, plain, (u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_84, c_100])).
% 7.45/2.58  tff(c_110, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_105])).
% 7.45/2.58  tff(c_133, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_110])).
% 7.45/2.58  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_133])).
% 7.45/2.58  tff(c_140, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_105])).
% 7.45/2.58  tff(c_28, plain, (![A_19]: (m1_subset_1(k3_yellow_0(A_19), u1_struct_0(A_19)) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.45/2.58  tff(c_149, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_140, c_28])).
% 7.45/2.58  tff(c_153, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_149])).
% 7.45/2.58  tff(c_161, plain, (![A_67, B_68]: (r2_hidden(A_67, B_68) | v1_xboole_0(B_68) | ~m1_subset_1(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.45/2.58  tff(c_74, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.45/2.58  tff(c_99, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_74])).
% 7.45/2.58  tff(c_164, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_161, c_99])).
% 7.45/2.58  tff(c_170, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_164])).
% 7.45/2.58  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_170])).
% 7.45/2.58  tff(c_173, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 7.45/2.58  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_173])).
% 7.45/2.58  tff(c_176, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 7.45/2.58  tff(c_260, plain, (![A_89]: (r2_hidden(k3_yellow_0('#skF_5'), A_89) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_89)))), inference(resolution, [status(thm)], [c_176, c_253])).
% 7.45/2.58  tff(c_325, plain, (![B_98, A_99]: (m1_subset_1(k3_yellow_0('#skF_5'), B_98) | ~r1_tarski(A_99, B_98) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_99)))), inference(resolution, [status(thm)], [c_260, c_215])).
% 7.45/2.58  tff(c_333, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_325])).
% 7.45/2.58  tff(c_335, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_333])).
% 7.45/2.58  tff(c_338, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_335])).
% 7.45/2.58  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_338])).
% 7.45/2.58  tff(c_344, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_333])).
% 7.45/2.58  tff(c_720, plain, (![A_136]: (r2_hidden(A_136, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(A_136, '#skF_6'))), inference(resolution, [status(thm)], [c_344, c_712])).
% 7.45/2.58  tff(c_742, plain, (![A_139]: (r2_hidden(A_139, '#skF_6') | ~m1_subset_1(A_139, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_720])).
% 7.45/2.58  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.45/2.58  tff(c_1080, plain, (![B_169]: (~r2_hidden('#skF_2'('#skF_6', B_169), B_169) | B_169='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', B_169), '#skF_6'))), inference(resolution, [status(thm)], [c_742, c_2])).
% 7.45/2.58  tff(c_1115, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(resolution, [status(thm)], [c_741, c_1080])).
% 7.45/2.58  tff(c_2075, plain, (~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(splitLeft, [status(thm)], [c_1115])).
% 7.45/2.58  tff(c_2427, plain, (![B_258]: (m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), B_258) | ~r1_tarski(u1_struct_0('#skF_5'), B_258) | u1_struct_0('#skF_5')='#skF_6')), inference(resolution, [status(thm)], [c_2327, c_2075])).
% 7.45/2.58  tff(c_2514, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_2427])).
% 7.45/2.58  tff(c_216, plain, (![A_75]: (m1_subset_1(A_75, u1_struct_0('#skF_5')) | ~r2_hidden(A_75, '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_210])).
% 7.45/2.58  tff(c_858, plain, (![A_151, B_152, A_153]: (r2_hidden(A_151, B_152) | v1_xboole_0(A_153) | ~m1_subset_1(A_151, A_153) | ~r1_tarski(A_153, B_152))), inference(resolution, [status(thm)], [c_24, c_712])).
% 7.45/2.58  tff(c_893, plain, (![A_75, B_152]: (r2_hidden(A_75, B_152) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r1_tarski(u1_struct_0('#skF_5'), B_152) | ~r2_hidden(A_75, '#skF_6'))), inference(resolution, [status(thm)], [c_216, c_858])).
% 7.45/2.58  tff(c_1181, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_893])).
% 7.45/2.58  tff(c_2521, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2514, c_1181])).
% 7.45/2.58  tff(c_2541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2521])).
% 7.45/2.58  tff(c_2543, plain, (u1_struct_0('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_2427])).
% 7.45/2.58  tff(c_2542, plain, (![B_258]: (m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), B_258) | ~r1_tarski(u1_struct_0('#skF_5'), B_258))), inference(splitRight, [status(thm)], [c_2427])).
% 7.45/2.58  tff(c_50, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.45/2.58  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.45/2.58  tff(c_60, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.45/2.58  tff(c_58, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.45/2.58  tff(c_30, plain, (![A_20, B_22]: (r1_orders_2(A_20, k3_yellow_0(A_20), B_22) | ~m1_subset_1(B_22, u1_struct_0(A_20)) | ~l1_orders_2(A_20) | ~v1_yellow_0(A_20) | ~v5_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.45/2.58  tff(c_1314, plain, (![D_196, B_197, A_198, C_199]: (r2_hidden(D_196, B_197) | ~r1_orders_2(A_198, C_199, D_196) | ~r2_hidden(C_199, B_197) | ~m1_subset_1(D_196, u1_struct_0(A_198)) | ~m1_subset_1(C_199, u1_struct_0(A_198)) | ~v13_waybel_0(B_197, A_198) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_orders_2(A_198))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.45/2.58  tff(c_2632, plain, (![B_263, B_264, A_265]: (r2_hidden(B_263, B_264) | ~r2_hidden(k3_yellow_0(A_265), B_264) | ~m1_subset_1(k3_yellow_0(A_265), u1_struct_0(A_265)) | ~v13_waybel_0(B_264, A_265) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_265))) | ~m1_subset_1(B_263, u1_struct_0(A_265)) | ~l1_orders_2(A_265) | ~v1_yellow_0(A_265) | ~v5_orders_2(A_265) | v2_struct_0(A_265))), inference(resolution, [status(thm)], [c_30, c_1314])).
% 7.45/2.58  tff(c_2646, plain, (![B_263, B_264]: (r2_hidden(B_263, B_264) | ~r2_hidden(k3_yellow_0('#skF_5'), B_264) | ~v13_waybel_0(B_264, '#skF_5') | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_263, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_216, c_2632])).
% 7.45/2.58  tff(c_2667, plain, (![B_263, B_264]: (r2_hidden(B_263, B_264) | ~r2_hidden(k3_yellow_0('#skF_5'), B_264) | ~v13_waybel_0(B_264, '#skF_5') | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_263, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_60, c_58, c_56, c_2646])).
% 7.45/2.58  tff(c_2966, plain, (![B_274, B_275]: (r2_hidden(B_274, B_275) | ~r2_hidden(k3_yellow_0('#skF_5'), B_275) | ~v13_waybel_0(B_275, '#skF_5') | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_274, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_2667])).
% 7.45/2.58  tff(c_3022, plain, (![B_274]: (r2_hidden(B_274, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_274, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_48, c_2966])).
% 7.45/2.58  tff(c_3045, plain, (![B_276]: (r2_hidden(B_276, '#skF_6') | ~m1_subset_1(B_276, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_176, c_3022])).
% 7.45/2.58  tff(c_3061, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_2542, c_3045])).
% 7.45/2.58  tff(c_3144, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3061])).
% 7.45/2.58  tff(c_413, plain, (![A_108, B_109]: (~r2_hidden('#skF_1'(A_108, B_109), A_108) | r2_hidden('#skF_2'(A_108, B_109), A_108) | B_109=A_108)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.45/2.58  tff(c_433, plain, (![A_108, B_109]: (m1_subset_1('#skF_2'(A_108, B_109), A_108) | ~r2_hidden('#skF_1'(A_108, B_109), A_108) | B_109=A_108)), inference(resolution, [status(thm)], [c_413, c_18])).
% 7.45/2.58  tff(c_3187, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_3144, c_433])).
% 7.45/2.58  tff(c_3206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2543, c_2075, c_3187])).
% 7.45/2.58  tff(c_3207, plain, (~m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_1115])).
% 7.45/2.58  tff(c_3214, plain, (~m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(splitLeft, [status(thm)], [c_3207])).
% 7.45/2.58  tff(c_3208, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_1115])).
% 7.45/2.58  tff(c_738, plain, (![A_136, B_15, A_14]: (r2_hidden(A_136, B_15) | v1_xboole_0(A_14) | ~m1_subset_1(A_136, A_14) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_24, c_712])).
% 7.45/2.58  tff(c_3210, plain, (![B_15]: (r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), B_15) | v1_xboole_0('#skF_6') | ~r1_tarski('#skF_6', B_15))), inference(resolution, [status(thm)], [c_3208, c_738])).
% 7.45/2.58  tff(c_3274, plain, (![B_279]: (r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), B_279) | ~r1_tarski('#skF_6', B_279))), inference(negUnitSimplification, [status(thm)], [c_54, c_3210])).
% 7.45/2.58  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.45/2.58  tff(c_3288, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_3274, c_4])).
% 7.45/2.58  tff(c_3309, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3288])).
% 7.45/2.58  tff(c_3374, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_3309])).
% 7.45/2.58  tff(c_3399, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3374, c_1181])).
% 7.45/2.58  tff(c_3419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_3399])).
% 7.45/2.58  tff(c_3420, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_3309])).
% 7.45/2.58  tff(c_3430, plain, (![B_15]: (m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), B_15) | ~r1_tarski(u1_struct_0('#skF_5'), B_15))), inference(resolution, [status(thm)], [c_3420, c_215])).
% 7.45/2.58  tff(c_3466, plain, (![B_284, B_285, A_286]: (r2_hidden(B_284, B_285) | ~r2_hidden(k3_yellow_0(A_286), B_285) | ~m1_subset_1(k3_yellow_0(A_286), u1_struct_0(A_286)) | ~v13_waybel_0(B_285, A_286) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_286))) | ~m1_subset_1(B_284, u1_struct_0(A_286)) | ~l1_orders_2(A_286) | ~v1_yellow_0(A_286) | ~v5_orders_2(A_286) | v2_struct_0(A_286))), inference(resolution, [status(thm)], [c_30, c_1314])).
% 7.45/2.58  tff(c_3480, plain, (![B_284, B_285]: (r2_hidden(B_284, B_285) | ~r2_hidden(k3_yellow_0('#skF_5'), B_285) | ~v13_waybel_0(B_285, '#skF_5') | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_284, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_216, c_3466])).
% 7.45/2.58  tff(c_3501, plain, (![B_284, B_285]: (r2_hidden(B_284, B_285) | ~r2_hidden(k3_yellow_0('#skF_5'), B_285) | ~v13_waybel_0(B_285, '#skF_5') | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_284, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_60, c_58, c_56, c_3480])).
% 7.45/2.58  tff(c_3630, plain, (![B_290, B_291]: (r2_hidden(B_290, B_291) | ~r2_hidden(k3_yellow_0('#skF_5'), B_291) | ~v13_waybel_0(B_291, '#skF_5') | ~m1_subset_1(B_291, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_290, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_3501])).
% 7.45/2.58  tff(c_3671, plain, (![B_290]: (r2_hidden(B_290, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_290, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_48, c_3630])).
% 7.45/2.58  tff(c_3689, plain, (![B_292]: (r2_hidden(B_292, '#skF_6') | ~m1_subset_1(B_292, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_176, c_3671])).
% 7.45/2.58  tff(c_3693, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_3430, c_3689])).
% 7.45/2.58  tff(c_3768, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3693])).
% 7.45/2.58  tff(c_3828, plain, (m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(resolution, [status(thm)], [c_3768, c_18])).
% 7.45/2.58  tff(c_3843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3214, c_3828])).
% 7.45/2.58  tff(c_3844, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_3207])).
% 7.45/2.58  tff(c_3851, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3844, c_1181])).
% 7.45/2.58  tff(c_3871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_3851])).
% 7.45/2.58  tff(c_3873, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_893])).
% 7.45/2.58  tff(c_614, plain, (![A_132, B_133]: (m1_subset_1('#skF_1'(A_132, B_133), B_133) | r2_hidden('#skF_2'(A_132, B_133), A_132) | B_133=A_132)), inference(resolution, [status(thm)], [c_291, c_18])).
% 7.45/2.58  tff(c_4834, plain, (![A_371, B_372, B_373]: (m1_subset_1('#skF_2'(A_371, B_372), B_373) | ~r1_tarski(A_371, B_373) | m1_subset_1('#skF_1'(A_371, B_372), B_372) | B_372=A_371)), inference(resolution, [status(thm)], [c_614, c_215])).
% 7.45/2.58  tff(c_384, plain, (![A_103, B_104]: (r2_hidden('#skF_1'(A_103, B_104), B_104) | ~r2_hidden('#skF_2'(A_103, B_104), B_104) | B_104=A_103)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.45/2.58  tff(c_4134, plain, (![A_332, B_333]: (r2_hidden('#skF_1'(A_332, B_333), B_333) | B_333=A_332 | v1_xboole_0(B_333) | ~m1_subset_1('#skF_2'(A_332, B_333), B_333))), inference(resolution, [status(thm)], [c_20, c_384])).
% 7.45/2.58  tff(c_4163, plain, (![A_332, B_333]: (m1_subset_1('#skF_1'(A_332, B_333), B_333) | B_333=A_332 | v1_xboole_0(B_333) | ~m1_subset_1('#skF_2'(A_332, B_333), B_333))), inference(resolution, [status(thm)], [c_4134, c_18])).
% 7.45/2.58  tff(c_4916, plain, (![B_373, A_371]: (v1_xboole_0(B_373) | ~r1_tarski(A_371, B_373) | m1_subset_1('#skF_1'(A_371, B_373), B_373) | B_373=A_371)), inference(resolution, [status(thm)], [c_4834, c_4163])).
% 7.45/2.58  tff(c_3966, plain, (![D_312, B_313, A_314, C_315]: (r2_hidden(D_312, B_313) | ~r1_orders_2(A_314, C_315, D_312) | ~r2_hidden(C_315, B_313) | ~m1_subset_1(D_312, u1_struct_0(A_314)) | ~m1_subset_1(C_315, u1_struct_0(A_314)) | ~v13_waybel_0(B_313, A_314) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0(A_314))) | ~l1_orders_2(A_314))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.45/2.58  tff(c_5847, plain, (![B_407, B_408, A_409]: (r2_hidden(B_407, B_408) | ~r2_hidden(k3_yellow_0(A_409), B_408) | ~m1_subset_1(k3_yellow_0(A_409), u1_struct_0(A_409)) | ~v13_waybel_0(B_408, A_409) | ~m1_subset_1(B_408, k1_zfmisc_1(u1_struct_0(A_409))) | ~m1_subset_1(B_407, u1_struct_0(A_409)) | ~l1_orders_2(A_409) | ~v1_yellow_0(A_409) | ~v5_orders_2(A_409) | v2_struct_0(A_409))), inference(resolution, [status(thm)], [c_30, c_3966])).
% 7.45/2.58  tff(c_5861, plain, (![B_407, B_408]: (r2_hidden(B_407, B_408) | ~r2_hidden(k3_yellow_0('#skF_5'), B_408) | ~v13_waybel_0(B_408, '#skF_5') | ~m1_subset_1(B_408, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_407, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_216, c_5847])).
% 7.45/2.58  tff(c_5882, plain, (![B_407, B_408]: (r2_hidden(B_407, B_408) | ~r2_hidden(k3_yellow_0('#skF_5'), B_408) | ~v13_waybel_0(B_408, '#skF_5') | ~m1_subset_1(B_408, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_407, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_60, c_58, c_56, c_5861])).
% 7.45/2.58  tff(c_5940, plain, (![B_413, B_414]: (r2_hidden(B_413, B_414) | ~r2_hidden(k3_yellow_0('#skF_5'), B_414) | ~v13_waybel_0(B_414, '#skF_5') | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_413, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_5882])).
% 7.45/2.58  tff(c_6008, plain, (![B_413]: (r2_hidden(B_413, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_413, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_48, c_5940])).
% 7.45/2.58  tff(c_6036, plain, (![B_415]: (r2_hidden(B_415, '#skF_6') | ~m1_subset_1(B_415, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_176, c_6008])).
% 7.45/2.58  tff(c_6072, plain, (![A_371]: (r2_hidden('#skF_1'(A_371, u1_struct_0('#skF_5')), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')) | ~r1_tarski(A_371, u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')=A_371)), inference(resolution, [status(thm)], [c_4916, c_6036])).
% 7.45/2.58  tff(c_6293, plain, (![A_421]: (r2_hidden('#skF_1'(A_421, u1_struct_0('#skF_5')), '#skF_6') | ~r1_tarski(A_421, u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')=A_421)), inference(negUnitSimplification, [status(thm)], [c_3873, c_6072])).
% 7.45/2.58  tff(c_6303, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~r1_tarski('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_6293, c_433])).
% 7.45/2.58  tff(c_6322, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6303])).
% 7.45/2.58  tff(c_6329, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_6322])).
% 7.45/2.58  tff(c_184, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.45/2.58  tff(c_189, plain, (u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_84, c_184])).
% 7.45/2.58  tff(c_194, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_189])).
% 7.45/2.58  tff(c_6357, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6329, c_194])).
% 7.45/2.58  tff(c_6367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_6357])).
% 7.45/2.58  tff(c_6369, plain, (u1_struct_0('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_6322])).
% 7.45/2.58  tff(c_6368, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_6322])).
% 7.45/2.58  tff(c_6371, plain, (![B_15]: (r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), B_15) | v1_xboole_0('#skF_6') | ~r1_tarski('#skF_6', B_15))), inference(resolution, [status(thm)], [c_6368, c_738])).
% 7.45/2.58  tff(c_6375, plain, (![B_422]: (r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), B_422) | ~r1_tarski('#skF_6', B_422))), inference(negUnitSimplification, [status(thm)], [c_54, c_6371])).
% 7.45/2.58  tff(c_407, plain, (![A_106, B_107]: (~r2_hidden('#skF_1'(A_106, B_107), A_106) | ~r2_hidden('#skF_2'(A_106, B_107), B_107) | B_107=A_106)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.45/2.58  tff(c_412, plain, (![B_13, B_107]: (~r2_hidden('#skF_2'(B_13, B_107), B_107) | B_13=B_107 | v1_xboole_0(B_13) | ~m1_subset_1('#skF_1'(B_13, B_107), B_13))), inference(resolution, [status(thm)], [c_20, c_407])).
% 7.45/2.58  tff(c_6378, plain, (u1_struct_0('#skF_5')='#skF_6' | v1_xboole_0('#skF_6') | ~m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_6375, c_412])).
% 7.45/2.58  tff(c_6402, plain, (u1_struct_0('#skF_5')='#skF_6' | v1_xboole_0('#skF_6') | ~m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6378])).
% 7.45/2.58  tff(c_6403, plain, (~m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_6369, c_6402])).
% 7.45/2.58  tff(c_6389, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_6375, c_4])).
% 7.45/2.58  tff(c_6411, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6389])).
% 7.45/2.58  tff(c_6412, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_6369, c_6411])).
% 7.45/2.58  tff(c_6546, plain, (m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_6412, c_18])).
% 7.45/2.58  tff(c_6035, plain, (![B_413]: (r2_hidden(B_413, '#skF_6') | ~m1_subset_1(B_413, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_176, c_6008])).
% 7.45/2.58  tff(c_6552, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(resolution, [status(thm)], [c_6546, c_6035])).
% 7.45/2.58  tff(c_6571, plain, (m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(resolution, [status(thm)], [c_6552, c_18])).
% 7.45/2.58  tff(c_6589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6403, c_6571])).
% 7.45/2.58  tff(c_6590, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_189])).
% 7.45/2.58  tff(c_177, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_68])).
% 7.45/2.58  tff(c_6592, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6590, c_177])).
% 7.45/2.58  tff(c_6596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_6592])).
% 7.45/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.58  
% 7.45/2.58  Inference rules
% 7.45/2.58  ----------------------
% 7.45/2.58  #Ref     : 0
% 7.45/2.58  #Sup     : 1409
% 7.45/2.58  #Fact    : 0
% 7.45/2.58  #Define  : 0
% 7.45/2.58  #Split   : 22
% 7.45/2.58  #Chain   : 0
% 7.45/2.58  #Close   : 0
% 7.45/2.58  
% 7.45/2.58  Ordering : KBO
% 7.45/2.58  
% 7.45/2.58  Simplification rules
% 7.45/2.58  ----------------------
% 7.45/2.58  #Subsume      : 214
% 7.45/2.58  #Demod        : 360
% 7.45/2.58  #Tautology    : 194
% 7.45/2.58  #SimpNegUnit  : 90
% 7.45/2.58  #BackRed      : 113
% 7.45/2.58  
% 7.45/2.58  #Partial instantiations: 0
% 7.45/2.58  #Strategies tried      : 1
% 7.45/2.58  
% 7.45/2.58  Timing (in seconds)
% 7.45/2.58  ----------------------
% 7.45/2.58  Preprocessing        : 0.33
% 7.45/2.58  Parsing              : 0.19
% 7.45/2.58  CNF conversion       : 0.03
% 7.45/2.58  Main loop            : 1.44
% 7.45/2.58  Inferencing          : 0.43
% 7.45/2.58  Reduction            : 0.38
% 7.45/2.59  Demodulation         : 0.24
% 7.45/2.59  BG Simplification    : 0.06
% 7.45/2.59  Subsumption          : 0.46
% 7.45/2.59  Abstraction          : 0.06
% 7.45/2.59  MUC search           : 0.00
% 7.45/2.59  Cooper               : 0.00
% 7.45/2.59  Total                : 1.83
% 7.45/2.59  Index Insertion      : 0.00
% 7.45/2.59  Index Deletion       : 0.00
% 7.45/2.59  Index Matching       : 0.00
% 7.45/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
