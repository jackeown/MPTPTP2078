%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1313+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:46 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 428 expanded)
%              Number of leaves         :   25 ( 162 expanded)
%              Depth                    :   11
%              Number of atoms          :  340 (1527 expanded)
%              Number of equality atoms :   23 ( 142 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
               => ( v3_pre_topc(C,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_804,plain,(
    ! [B_235,A_236] :
      ( l1_pre_topc(B_235)
      | ~ m1_pre_topc(B_235,A_236)
      | ~ l1_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_807,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_804])).

tff(c_810,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_807])).

tff(c_58,plain,(
    ! [B_66,A_67] :
      ( l1_pre_topc(B_66)
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_61,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_64,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_61])).

tff(c_52,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | v3_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_57,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k9_subset_1(u1_struct_0('#skF_5'),'#skF_7',k2_struct_0('#skF_5')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_66,plain,(
    k9_subset_1(u1_struct_0('#skF_5'),'#skF_7',k2_struct_0('#skF_5')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_56,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_65,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_72,plain,(
    ! [B_70,A_71] :
      ( r2_hidden(B_70,u1_pre_topc(A_71))
      | ~ v3_pre_topc(B_70,A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,
    ( r2_hidden('#skF_6',u1_pre_topc('#skF_5'))
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_84,plain,
    ( r2_hidden('#skF_6',u1_pre_topc('#skF_5'))
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_78])).

tff(c_85,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_86,plain,(
    ! [B_72,A_73] :
      ( v3_pre_topc(B_72,A_73)
      | ~ r2_hidden(B_72,u1_pre_topc(A_73))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ r2_hidden('#skF_6',u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_86])).

tff(c_98,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ r2_hidden('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_92])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_98])).

tff(c_75,plain,
    ( r2_hidden('#skF_7',u1_pre_topc('#skF_4'))
    | ~ v3_pre_topc('#skF_7','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_65,c_72])).

tff(c_81,plain,(
    r2_hidden('#skF_7',u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_57,c_75])).

tff(c_214,plain,(
    ! [B_110,D_111,A_112] :
      ( r2_hidden(k9_subset_1(u1_struct_0(B_110),D_111,k2_struct_0(B_110)),u1_pre_topc(B_110))
      | ~ r2_hidden(D_111,u1_pre_topc(A_112))
      | ~ m1_subset_1(D_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_110),D_111,k2_struct_0(B_110)),k1_zfmisc_1(u1_struct_0(B_110)))
      | ~ m1_pre_topc(B_110,A_112)
      | ~ l1_pre_topc(B_110)
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_224,plain,(
    ! [B_110] :
      ( r2_hidden(k9_subset_1(u1_struct_0(B_110),'#skF_7',k2_struct_0(B_110)),u1_pre_topc(B_110))
      | ~ r2_hidden('#skF_7',u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_110),'#skF_7',k2_struct_0(B_110)),k1_zfmisc_1(u1_struct_0(B_110)))
      | ~ m1_pre_topc(B_110,'#skF_4')
      | ~ l1_pre_topc(B_110)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_214])).

tff(c_237,plain,(
    ! [B_113] :
      ( r2_hidden(k9_subset_1(u1_struct_0(B_113),'#skF_7',k2_struct_0(B_113)),u1_pre_topc(B_113))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_113),'#skF_7',k2_struct_0(B_113)),k1_zfmisc_1(u1_struct_0(B_113)))
      | ~ m1_pre_topc(B_113,'#skF_4')
      | ~ l1_pre_topc(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_224])).

tff(c_240,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_7',k2_struct_0('#skF_5')),u1_pre_topc('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_237])).

tff(c_242,plain,(
    r2_hidden('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_38,c_36,c_66,c_240])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_242])).

tff(c_246,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_42,plain,(
    ! [D_65] :
      ( k9_subset_1(u1_struct_0('#skF_5'),D_65,k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc(D_65,'#skF_4')
      | ~ m1_subset_1(D_65,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_6','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_263,plain,(
    ! [D_116] :
      ( k9_subset_1(u1_struct_0('#skF_5'),D_116,k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc(D_116,'#skF_4')
      | ~ m1_subset_1(D_116,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_42])).

tff(c_266,plain,
    ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_7',k2_struct_0('#skF_5')) != '#skF_6'
    | ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_65,c_263])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_66,c_266])).

tff(c_271,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_275,plain,(
    ! [B_119,A_120] :
      ( r2_hidden(B_119,u1_pre_topc(A_120))
      | ~ v3_pre_topc(B_119,A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_281,plain,
    ( r2_hidden('#skF_6',u1_pre_topc('#skF_5'))
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_275])).

tff(c_287,plain,(
    r2_hidden('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_271,c_281])).

tff(c_30,plain,(
    ! [A_4,B_26,C_37] :
      ( r2_hidden('#skF_1'(A_4,B_26,C_37),u1_pre_topc(A_4))
      | ~ r2_hidden(C_37,u1_pre_topc(B_26))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ m1_pre_topc(B_26,A_4)
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_336,plain,(
    ! [A_134,B_135,C_136] :
      ( m1_subset_1('#skF_1'(A_134,B_135,C_136),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ r2_hidden(C_136,u1_pre_topc(B_135))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(B_135)))
      | ~ m1_pre_topc(B_135,A_134)
      | ~ l1_pre_topc(B_135)
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_pre_topc(B_3,A_1)
      | ~ r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_429,plain,(
    ! [A_155,B_156,C_157] :
      ( v3_pre_topc('#skF_1'(A_155,B_156,C_157),A_155)
      | ~ r2_hidden('#skF_1'(A_155,B_156,C_157),u1_pre_topc(A_155))
      | ~ r2_hidden(C_157,u1_pre_topc(B_156))
      | ~ m1_subset_1(C_157,k1_zfmisc_1(u1_struct_0(B_156)))
      | ~ m1_pre_topc(B_156,A_155)
      | ~ l1_pre_topc(B_156)
      | ~ l1_pre_topc(A_155) ) ),
    inference(resolution,[status(thm)],[c_336,c_2])).

tff(c_434,plain,(
    ! [A_158,B_159,C_160] :
      ( v3_pre_topc('#skF_1'(A_158,B_159,C_160),A_158)
      | ~ r2_hidden(C_160,u1_pre_topc(B_159))
      | ~ m1_subset_1(C_160,k1_zfmisc_1(u1_struct_0(B_159)))
      | ~ m1_pre_topc(B_159,A_158)
      | ~ l1_pre_topc(B_159)
      | ~ l1_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_30,c_429])).

tff(c_446,plain,(
    ! [A_158] :
      ( v3_pre_topc('#skF_1'(A_158,'#skF_5','#skF_6'),A_158)
      | ~ r2_hidden('#skF_6',u1_pre_topc('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_158)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_36,c_434])).

tff(c_456,plain,(
    ! [A_158] :
      ( v3_pre_topc('#skF_1'(A_158,'#skF_5','#skF_6'),A_158)
      | ~ m1_pre_topc('#skF_5',A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_287,c_446])).

tff(c_28,plain,(
    ! [B_26,A_4,C_37] :
      ( k9_subset_1(u1_struct_0(B_26),'#skF_1'(A_4,B_26,C_37),k2_struct_0(B_26)) = C_37
      | ~ r2_hidden(C_37,u1_pre_topc(B_26))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ m1_pre_topc(B_26,A_4)
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_302,plain,(
    ! [D_65] :
      ( k9_subset_1(u1_struct_0('#skF_5'),D_65,k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc(D_65,'#skF_4')
      | ~ m1_subset_1(D_65,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_42])).

tff(c_340,plain,(
    ! [B_135,C_136] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_4',B_135,C_136),k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_135,C_136),'#skF_4')
      | ~ r2_hidden(C_136,u1_pre_topc(B_135))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(B_135)))
      | ~ m1_pre_topc(B_135,'#skF_4')
      | ~ l1_pre_topc(B_135)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_336,c_302])).

tff(c_502,plain,(
    ! [B_173,C_174] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_4',B_173,C_174),k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_173,C_174),'#skF_4')
      | ~ r2_hidden(C_174,u1_pre_topc(B_173))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(B_173)))
      | ~ m1_pre_topc(B_173,'#skF_4')
      | ~ l1_pre_topc(B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_340])).

tff(c_506,plain,(
    ! [C_37] :
      ( C_37 != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5',C_37),'#skF_4')
      | ~ r2_hidden(C_37,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ r2_hidden(C_37,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_502])).

tff(c_510,plain,(
    ! [C_175] :
      ( C_175 != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5',C_175),'#skF_4')
      | ~ r2_hidden(C_175,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_64,c_38,c_64,c_38,c_506])).

tff(c_529,plain,
    ( ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ r2_hidden('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_510])).

tff(c_544,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_529])).

tff(c_552,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_456,c_544])).

tff(c_556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_552])).

tff(c_557,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_568,plain,(
    ! [B_183,A_184] :
      ( r2_hidden(B_183,u1_pre_topc(A_184))
      | ~ v3_pre_topc(B_183,A_184)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_571,plain,
    ( r2_hidden('#skF_6',u1_pre_topc('#skF_5'))
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_568])).

tff(c_574,plain,(
    r2_hidden('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_557,c_571])).

tff(c_604,plain,(
    ! [A_196,B_197,C_198] :
      ( m1_subset_1('#skF_1'(A_196,B_197,C_198),k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ r2_hidden(C_198,u1_pre_topc(B_197))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(u1_struct_0(B_197)))
      | ~ m1_pre_topc(B_197,A_196)
      | ~ l1_pre_topc(B_197)
      | ~ l1_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_728,plain,(
    ! [A_225,B_226,C_227] :
      ( v3_pre_topc('#skF_1'(A_225,B_226,C_227),A_225)
      | ~ r2_hidden('#skF_1'(A_225,B_226,C_227),u1_pre_topc(A_225))
      | ~ r2_hidden(C_227,u1_pre_topc(B_226))
      | ~ m1_subset_1(C_227,k1_zfmisc_1(u1_struct_0(B_226)))
      | ~ m1_pre_topc(B_226,A_225)
      | ~ l1_pre_topc(B_226)
      | ~ l1_pre_topc(A_225) ) ),
    inference(resolution,[status(thm)],[c_604,c_2])).

tff(c_776,plain,(
    ! [A_231,B_232,C_233] :
      ( v3_pre_topc('#skF_1'(A_231,B_232,C_233),A_231)
      | ~ r2_hidden(C_233,u1_pre_topc(B_232))
      | ~ m1_subset_1(C_233,k1_zfmisc_1(u1_struct_0(B_232)))
      | ~ m1_pre_topc(B_232,A_231)
      | ~ l1_pre_topc(B_232)
      | ~ l1_pre_topc(A_231) ) ),
    inference(resolution,[status(thm)],[c_30,c_728])).

tff(c_786,plain,(
    ! [A_231] :
      ( v3_pre_topc('#skF_1'(A_231,'#skF_5','#skF_6'),A_231)
      | ~ r2_hidden('#skF_6',u1_pre_topc('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_231)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_231) ) ),
    inference(resolution,[status(thm)],[c_36,c_776])).

tff(c_794,plain,(
    ! [A_234] :
      ( v3_pre_topc('#skF_1'(A_234,'#skF_5','#skF_6'),A_234)
      | ~ m1_pre_topc('#skF_5',A_234)
      | ~ l1_pre_topc(A_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_574,c_786])).

tff(c_576,plain,(
    ! [D_65] :
      ( k9_subset_1(u1_struct_0('#skF_5'),D_65,k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc(D_65,'#skF_4')
      | ~ m1_subset_1(D_65,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_42])).

tff(c_608,plain,(
    ! [B_197,C_198] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_4',B_197,C_198),k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_197,C_198),'#skF_4')
      | ~ r2_hidden(C_198,u1_pre_topc(B_197))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(u1_struct_0(B_197)))
      | ~ m1_pre_topc(B_197,'#skF_4')
      | ~ l1_pre_topc(B_197)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_604,c_576])).

tff(c_733,plain,(
    ! [B_228,C_229] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_4',B_228,C_229),k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_228,C_229),'#skF_4')
      | ~ r2_hidden(C_229,u1_pre_topc(B_228))
      | ~ m1_subset_1(C_229,k1_zfmisc_1(u1_struct_0(B_228)))
      | ~ m1_pre_topc(B_228,'#skF_4')
      | ~ l1_pre_topc(B_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_608])).

tff(c_737,plain,(
    ! [C_37] :
      ( C_37 != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5',C_37),'#skF_4')
      | ~ r2_hidden(C_37,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ r2_hidden(C_37,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_733])).

tff(c_741,plain,(
    ! [C_230] :
      ( C_230 != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5',C_230),'#skF_4')
      | ~ r2_hidden(C_230,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_230,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_64,c_38,c_64,c_38,c_737])).

tff(c_760,plain,
    ( ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ r2_hidden('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_741])).

tff(c_775,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_760])).

tff(c_797,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_794,c_775])).

tff(c_801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_797])).

tff(c_802,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_821,plain,(
    ! [B_241,A_242] :
      ( r2_hidden(B_241,u1_pre_topc(A_242))
      | ~ v3_pre_topc(B_241,A_242)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_824,plain,
    ( r2_hidden('#skF_6',u1_pre_topc('#skF_5'))
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_821])).

tff(c_827,plain,(
    r2_hidden('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_802,c_824])).

tff(c_856,plain,(
    ! [A_254,B_255,C_256] :
      ( m1_subset_1('#skF_1'(A_254,B_255,C_256),k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ r2_hidden(C_256,u1_pre_topc(B_255))
      | ~ m1_subset_1(C_256,k1_zfmisc_1(u1_struct_0(B_255)))
      | ~ m1_pre_topc(B_255,A_254)
      | ~ l1_pre_topc(B_255)
      | ~ l1_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_980,plain,(
    ! [A_283,B_284,C_285] :
      ( v3_pre_topc('#skF_1'(A_283,B_284,C_285),A_283)
      | ~ r2_hidden('#skF_1'(A_283,B_284,C_285),u1_pre_topc(A_283))
      | ~ r2_hidden(C_285,u1_pre_topc(B_284))
      | ~ m1_subset_1(C_285,k1_zfmisc_1(u1_struct_0(B_284)))
      | ~ m1_pre_topc(B_284,A_283)
      | ~ l1_pre_topc(B_284)
      | ~ l1_pre_topc(A_283) ) ),
    inference(resolution,[status(thm)],[c_856,c_2])).

tff(c_1028,plain,(
    ! [A_289,B_290,C_291] :
      ( v3_pre_topc('#skF_1'(A_289,B_290,C_291),A_289)
      | ~ r2_hidden(C_291,u1_pre_topc(B_290))
      | ~ m1_subset_1(C_291,k1_zfmisc_1(u1_struct_0(B_290)))
      | ~ m1_pre_topc(B_290,A_289)
      | ~ l1_pre_topc(B_290)
      | ~ l1_pre_topc(A_289) ) ),
    inference(resolution,[status(thm)],[c_30,c_980])).

tff(c_1038,plain,(
    ! [A_289] :
      ( v3_pre_topc('#skF_1'(A_289,'#skF_5','#skF_6'),A_289)
      | ~ r2_hidden('#skF_6',u1_pre_topc('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_289)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_289) ) ),
    inference(resolution,[status(thm)],[c_36,c_1028])).

tff(c_1046,plain,(
    ! [A_292] :
      ( v3_pre_topc('#skF_1'(A_292,'#skF_5','#skF_6'),A_292)
      | ~ m1_pre_topc('#skF_5',A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_827,c_1038])).

tff(c_829,plain,(
    ! [D_65] :
      ( k9_subset_1(u1_struct_0('#skF_5'),D_65,k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc(D_65,'#skF_4')
      | ~ m1_subset_1(D_65,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_802,c_42])).

tff(c_860,plain,(
    ! [B_255,C_256] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_4',B_255,C_256),k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_255,C_256),'#skF_4')
      | ~ r2_hidden(C_256,u1_pre_topc(B_255))
      | ~ m1_subset_1(C_256,k1_zfmisc_1(u1_struct_0(B_255)))
      | ~ m1_pre_topc(B_255,'#skF_4')
      | ~ l1_pre_topc(B_255)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_856,c_829])).

tff(c_985,plain,(
    ! [B_286,C_287] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_4',B_286,C_287),k2_struct_0('#skF_5')) != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_286,C_287),'#skF_4')
      | ~ r2_hidden(C_287,u1_pre_topc(B_286))
      | ~ m1_subset_1(C_287,k1_zfmisc_1(u1_struct_0(B_286)))
      | ~ m1_pre_topc(B_286,'#skF_4')
      | ~ l1_pre_topc(B_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_860])).

tff(c_989,plain,(
    ! [C_37] :
      ( C_37 != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5',C_37),'#skF_4')
      | ~ r2_hidden(C_37,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ r2_hidden(C_37,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_985])).

tff(c_993,plain,(
    ! [C_288] :
      ( C_288 != '#skF_6'
      | ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5',C_288),'#skF_4')
      | ~ r2_hidden(C_288,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_288,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_810,c_38,c_810,c_38,c_989])).

tff(c_1012,plain,
    ( ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ r2_hidden('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_993])).

tff(c_1027,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_1012])).

tff(c_1049,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1046,c_1027])).

tff(c_1053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1049])).

%------------------------------------------------------------------------------
