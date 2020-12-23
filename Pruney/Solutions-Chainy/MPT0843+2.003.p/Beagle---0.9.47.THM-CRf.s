%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:40 EST 2020

% Result     : Theorem 12.44s
% Output     : CNFRefutation 12.44s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 283 expanded)
%              Number of leaves         :   23 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          :  159 ( 797 expanded)
%              Number of equality atoms :    3 (  45 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ! [D] :
                  ( r2_hidden(D,A)
                 => k11_relat_1(B,D) = k11_relat_1(C,D) )
             => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

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

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ! [D] :
          ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( r2_relset_1(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r2_hidden(k4_tarski(E,F),C)
                    <=> r2_hidden(k4_tarski(E,F),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).

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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_42])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_45,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_42])).

tff(c_51,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_45])).

tff(c_657,plain,(
    ! [A_258,B_259,C_260,D_261] :
      ( r2_hidden(k4_tarski('#skF_1'(A_258,B_259,C_260,D_261),'#skF_2'(A_258,B_259,C_260,D_261)),C_260)
      | r2_hidden(k4_tarski('#skF_1'(A_258,B_259,C_260,D_261),'#skF_2'(A_258,B_259,C_260,D_261)),D_261)
      | r2_relset_1(A_258,B_259,C_260,D_261)
      | ~ m1_subset_1(D_261,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4206,plain,(
    ! [D_607,B_605,C_603,A_606,A_604] :
      ( r2_hidden(k4_tarski('#skF_1'(A_604,B_605,C_603,D_607),'#skF_2'(A_604,B_605,C_603,D_607)),A_606)
      | ~ m1_subset_1(D_607,k1_zfmisc_1(A_606))
      | r2_hidden(k4_tarski('#skF_1'(A_604,B_605,C_603,D_607),'#skF_2'(A_604,B_605,C_603,D_607)),C_603)
      | r2_relset_1(A_604,B_605,C_603,D_607)
      | ~ m1_subset_1(D_607,k1_zfmisc_1(k2_zfmisc_1(A_604,B_605)))
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_604,B_605))) ) ),
    inference(resolution,[status(thm)],[c_657,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6924,plain,(
    ! [D_1093,C_1095,D_1094,C_1096,A_1097,B_1092] :
      ( r2_hidden('#skF_1'(A_1097,B_1092,C_1096,D_1093),C_1095)
      | ~ m1_subset_1(D_1093,k1_zfmisc_1(k2_zfmisc_1(C_1095,D_1094)))
      | r2_hidden(k4_tarski('#skF_1'(A_1097,B_1092,C_1096,D_1093),'#skF_2'(A_1097,B_1092,C_1096,D_1093)),C_1096)
      | r2_relset_1(A_1097,B_1092,C_1096,D_1093)
      | ~ m1_subset_1(D_1093,k1_zfmisc_1(k2_zfmisc_1(A_1097,B_1092)))
      | ~ m1_subset_1(C_1096,k1_zfmisc_1(k2_zfmisc_1(A_1097,B_1092))) ) ),
    inference(resolution,[status(thm)],[c_4206,c_6])).

tff(c_6931,plain,(
    ! [A_1098,B_1099,C_1100] :
      ( r2_hidden('#skF_1'(A_1098,B_1099,C_1100,'#skF_5'),'#skF_3')
      | r2_hidden(k4_tarski('#skF_1'(A_1098,B_1099,C_1100,'#skF_5'),'#skF_2'(A_1098,B_1099,C_1100,'#skF_5')),C_1100)
      | r2_relset_1(A_1098,B_1099,C_1100,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_1098,B_1099)))
      | ~ m1_subset_1(C_1100,k1_zfmisc_1(k2_zfmisc_1(A_1098,B_1099))) ) ),
    inference(resolution,[status(thm)],[c_38,c_6924])).

tff(c_16,plain,(
    ! [B_15,C_16,A_14] :
      ( r2_hidden(B_15,k11_relat_1(C_16,A_14))
      | ~ r2_hidden(k4_tarski(A_14,B_15),C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7249,plain,(
    ! [A_1116,B_1117,C_1118] :
      ( r2_hidden('#skF_2'(A_1116,B_1117,C_1118,'#skF_5'),k11_relat_1(C_1118,'#skF_1'(A_1116,B_1117,C_1118,'#skF_5')))
      | ~ v1_relat_1(C_1118)
      | r2_hidden('#skF_1'(A_1116,B_1117,C_1118,'#skF_5'),'#skF_3')
      | r2_relset_1(A_1116,B_1117,C_1118,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_1116,B_1117)))
      | ~ m1_subset_1(C_1118,k1_zfmisc_1(k2_zfmisc_1(A_1116,B_1117))) ) ),
    inference(resolution,[status(thm)],[c_6931,c_16])).

tff(c_60,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden(k4_tarski(A_68,B_69),C_70)
      | ~ r2_hidden(B_69,k11_relat_1(C_70,A_68))
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_134,plain,(
    ! [A_87,B_88,A_89,C_90] :
      ( r2_hidden(k4_tarski(A_87,B_88),A_89)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(A_89))
      | ~ r2_hidden(B_88,k11_relat_1(C_90,A_87))
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_60,c_8])).

tff(c_138,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(k4_tarski(A_87,B_88),k2_zfmisc_1('#skF_3','#skF_3'))
      | ~ r2_hidden(B_88,k11_relat_1('#skF_4',A_87))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_134])).

tff(c_176,plain,(
    ! [A_97,B_98] :
      ( r2_hidden(k4_tarski(A_97,B_98),k2_zfmisc_1('#skF_3','#skF_3'))
      | ~ r2_hidden(B_98,k11_relat_1('#skF_4',A_97)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_138])).

tff(c_193,plain,(
    ! [A_97,B_98] :
      ( r2_hidden(A_97,'#skF_3')
      | ~ r2_hidden(B_98,k11_relat_1('#skF_4',A_97)) ) ),
    inference(resolution,[status(thm)],[c_176,c_6])).

tff(c_7328,plain,(
    ! [A_1116,B_1117] :
      ( ~ v1_relat_1('#skF_4')
      | r2_hidden('#skF_1'(A_1116,B_1117,'#skF_4','#skF_5'),'#skF_3')
      | r2_relset_1(A_1116,B_1117,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_1116,B_1117)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1116,B_1117))) ) ),
    inference(resolution,[status(thm)],[c_7249,c_193])).

tff(c_7391,plain,(
    ! [A_1119,B_1120] :
      ( r2_hidden('#skF_1'(A_1119,B_1120,'#skF_4','#skF_5'),'#skF_3')
      | r2_relset_1(A_1119,B_1120,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_1119,B_1120)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1119,B_1120))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_7328])).

tff(c_7394,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_38,c_7391])).

tff(c_7397,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7394])).

tff(c_7398,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_7397])).

tff(c_36,plain,(
    ! [D_48] :
      ( k11_relat_1('#skF_5',D_48) = k11_relat_1('#skF_4',D_48)
      | ~ r2_hidden(D_48,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7405,plain,(
    k11_relat_1('#skF_5','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')) = k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_7398,c_36])).

tff(c_1425,plain,(
    ! [A_373,B_374,C_375,D_376] :
      ( r2_hidden('#skF_2'(A_373,B_374,C_375,D_376),k11_relat_1(D_376,'#skF_1'(A_373,B_374,C_375,D_376)))
      | ~ v1_relat_1(D_376)
      | r2_hidden(k4_tarski('#skF_1'(A_373,B_374,C_375,D_376),'#skF_2'(A_373,B_374,C_375,D_376)),C_375)
      | r2_relset_1(A_373,B_374,C_375,D_376)
      | ~ m1_subset_1(D_376,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374)))
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374))) ) ),
    inference(resolution,[status(thm)],[c_657,c_16])).

tff(c_11852,plain,(
    ! [A_1531,B_1532,C_1533,D_1534] :
      ( r2_hidden('#skF_2'(A_1531,B_1532,C_1533,D_1534),k11_relat_1(C_1533,'#skF_1'(A_1531,B_1532,C_1533,D_1534)))
      | ~ v1_relat_1(C_1533)
      | r2_hidden('#skF_2'(A_1531,B_1532,C_1533,D_1534),k11_relat_1(D_1534,'#skF_1'(A_1531,B_1532,C_1533,D_1534)))
      | ~ v1_relat_1(D_1534)
      | r2_relset_1(A_1531,B_1532,C_1533,D_1534)
      | ~ m1_subset_1(D_1534,k1_zfmisc_1(k2_zfmisc_1(A_1531,B_1532)))
      | ~ m1_subset_1(C_1533,k1_zfmisc_1(k2_zfmisc_1(A_1531,B_1532))) ) ),
    inference(resolution,[status(thm)],[c_1425,c_16])).

tff(c_12053,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_4')
    | r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7405,c_11852])).

tff(c_12129,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_51,c_54,c_12053])).

tff(c_12130,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_12129])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden(k4_tarski(A_14,B_15),C_16)
      | ~ r2_hidden(B_15,k11_relat_1(C_16,A_14))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_500,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_211,B_212,C_213,D_214),'#skF_2'(A_211,B_212,C_213,D_214)),D_214)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_211,B_212,C_213,D_214),'#skF_2'(A_211,B_212,C_213,D_214)),C_213)
      | r2_relset_1(A_211,B_212,C_213,D_214)
      | ~ m1_subset_1(D_214,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212)))
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1307,plain,(
    ! [A_334,B_335,C_336,C_337] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_334,B_335,C_336,C_337),'#skF_2'(A_334,B_335,C_336,C_337)),C_336)
      | r2_relset_1(A_334,B_335,C_336,C_337)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335)))
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335)))
      | ~ r2_hidden('#skF_2'(A_334,B_335,C_336,C_337),k11_relat_1(C_337,'#skF_1'(A_334,B_335,C_336,C_337)))
      | ~ v1_relat_1(C_337) ) ),
    inference(resolution,[status(thm)],[c_14,c_500])).

tff(c_13230,plain,(
    ! [A_1591,B_1592,C_1593,C_1594] :
      ( r2_relset_1(A_1591,B_1592,C_1593,C_1594)
      | ~ m1_subset_1(C_1594,k1_zfmisc_1(k2_zfmisc_1(A_1591,B_1592)))
      | ~ m1_subset_1(C_1593,k1_zfmisc_1(k2_zfmisc_1(A_1591,B_1592)))
      | ~ r2_hidden('#skF_2'(A_1591,B_1592,C_1593,C_1594),k11_relat_1(C_1594,'#skF_1'(A_1591,B_1592,C_1593,C_1594)))
      | ~ v1_relat_1(C_1594)
      | ~ r2_hidden('#skF_2'(A_1591,B_1592,C_1593,C_1594),k11_relat_1(C_1593,'#skF_1'(A_1591,B_1592,C_1593,C_1594)))
      | ~ v1_relat_1(C_1593) ) ),
    inference(resolution,[status(thm)],[c_14,c_1307])).

tff(c_13255,plain,
    ( r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7405,c_13230])).

tff(c_13327,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_12130,c_51,c_12130,c_40,c_38,c_13255])).

tff(c_13329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_13327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:21:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.44/5.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.44/5.55  
% 12.44/5.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.44/5.55  %$ r2_relset_1 > r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 12.44/5.55  
% 12.44/5.55  %Foreground sorts:
% 12.44/5.55  
% 12.44/5.55  
% 12.44/5.55  %Background operators:
% 12.44/5.55  
% 12.44/5.55  
% 12.44/5.55  %Foreground operators:
% 12.44/5.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.44/5.55  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 12.44/5.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.44/5.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.44/5.55  tff('#skF_5', type, '#skF_5': $i).
% 12.44/5.55  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 12.44/5.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 12.44/5.55  tff('#skF_3', type, '#skF_3': $i).
% 12.44/5.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.44/5.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.44/5.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.44/5.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.44/5.55  tff('#skF_4', type, '#skF_4': $i).
% 12.44/5.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.44/5.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 12.44/5.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.44/5.55  
% 12.44/5.57  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relset_1)).
% 12.44/5.57  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.44/5.57  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.44/5.57  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (r2_hidden(k4_tarski(E, F), C) <=> r2_hidden(k4_tarski(E, F), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relset_1)).
% 12.44/5.57  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 12.44/5.57  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 12.44/5.57  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 12.44/5.57  tff(c_34, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.44/5.57  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.44/5.57  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.44/5.57  tff(c_42, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.44/5.57  tff(c_48, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_42])).
% 12.44/5.57  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48])).
% 12.44/5.57  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.44/5.57  tff(c_45, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_42])).
% 12.44/5.57  tff(c_51, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_45])).
% 12.44/5.57  tff(c_657, plain, (![A_258, B_259, C_260, D_261]: (r2_hidden(k4_tarski('#skF_1'(A_258, B_259, C_260, D_261), '#skF_2'(A_258, B_259, C_260, D_261)), C_260) | r2_hidden(k4_tarski('#skF_1'(A_258, B_259, C_260, D_261), '#skF_2'(A_258, B_259, C_260, D_261)), D_261) | r2_relset_1(A_258, B_259, C_260, D_261) | ~m1_subset_1(D_261, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.44/5.57  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.44/5.57  tff(c_4206, plain, (![D_607, B_605, C_603, A_606, A_604]: (r2_hidden(k4_tarski('#skF_1'(A_604, B_605, C_603, D_607), '#skF_2'(A_604, B_605, C_603, D_607)), A_606) | ~m1_subset_1(D_607, k1_zfmisc_1(A_606)) | r2_hidden(k4_tarski('#skF_1'(A_604, B_605, C_603, D_607), '#skF_2'(A_604, B_605, C_603, D_607)), C_603) | r2_relset_1(A_604, B_605, C_603, D_607) | ~m1_subset_1(D_607, k1_zfmisc_1(k2_zfmisc_1(A_604, B_605))) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_604, B_605))))), inference(resolution, [status(thm)], [c_657, c_8])).
% 12.44/5.57  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.44/5.57  tff(c_6924, plain, (![D_1093, C_1095, D_1094, C_1096, A_1097, B_1092]: (r2_hidden('#skF_1'(A_1097, B_1092, C_1096, D_1093), C_1095) | ~m1_subset_1(D_1093, k1_zfmisc_1(k2_zfmisc_1(C_1095, D_1094))) | r2_hidden(k4_tarski('#skF_1'(A_1097, B_1092, C_1096, D_1093), '#skF_2'(A_1097, B_1092, C_1096, D_1093)), C_1096) | r2_relset_1(A_1097, B_1092, C_1096, D_1093) | ~m1_subset_1(D_1093, k1_zfmisc_1(k2_zfmisc_1(A_1097, B_1092))) | ~m1_subset_1(C_1096, k1_zfmisc_1(k2_zfmisc_1(A_1097, B_1092))))), inference(resolution, [status(thm)], [c_4206, c_6])).
% 12.44/5.57  tff(c_6931, plain, (![A_1098, B_1099, C_1100]: (r2_hidden('#skF_1'(A_1098, B_1099, C_1100, '#skF_5'), '#skF_3') | r2_hidden(k4_tarski('#skF_1'(A_1098, B_1099, C_1100, '#skF_5'), '#skF_2'(A_1098, B_1099, C_1100, '#skF_5')), C_1100) | r2_relset_1(A_1098, B_1099, C_1100, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_1098, B_1099))) | ~m1_subset_1(C_1100, k1_zfmisc_1(k2_zfmisc_1(A_1098, B_1099))))), inference(resolution, [status(thm)], [c_38, c_6924])).
% 12.44/5.57  tff(c_16, plain, (![B_15, C_16, A_14]: (r2_hidden(B_15, k11_relat_1(C_16, A_14)) | ~r2_hidden(k4_tarski(A_14, B_15), C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.44/5.57  tff(c_7249, plain, (![A_1116, B_1117, C_1118]: (r2_hidden('#skF_2'(A_1116, B_1117, C_1118, '#skF_5'), k11_relat_1(C_1118, '#skF_1'(A_1116, B_1117, C_1118, '#skF_5'))) | ~v1_relat_1(C_1118) | r2_hidden('#skF_1'(A_1116, B_1117, C_1118, '#skF_5'), '#skF_3') | r2_relset_1(A_1116, B_1117, C_1118, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_1116, B_1117))) | ~m1_subset_1(C_1118, k1_zfmisc_1(k2_zfmisc_1(A_1116, B_1117))))), inference(resolution, [status(thm)], [c_6931, c_16])).
% 12.44/5.57  tff(c_60, plain, (![A_68, B_69, C_70]: (r2_hidden(k4_tarski(A_68, B_69), C_70) | ~r2_hidden(B_69, k11_relat_1(C_70, A_68)) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.44/5.57  tff(c_134, plain, (![A_87, B_88, A_89, C_90]: (r2_hidden(k4_tarski(A_87, B_88), A_89) | ~m1_subset_1(C_90, k1_zfmisc_1(A_89)) | ~r2_hidden(B_88, k11_relat_1(C_90, A_87)) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_60, c_8])).
% 12.44/5.57  tff(c_138, plain, (![A_87, B_88]: (r2_hidden(k4_tarski(A_87, B_88), k2_zfmisc_1('#skF_3', '#skF_3')) | ~r2_hidden(B_88, k11_relat_1('#skF_4', A_87)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_134])).
% 12.44/5.57  tff(c_176, plain, (![A_97, B_98]: (r2_hidden(k4_tarski(A_97, B_98), k2_zfmisc_1('#skF_3', '#skF_3')) | ~r2_hidden(B_98, k11_relat_1('#skF_4', A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_138])).
% 12.44/5.57  tff(c_193, plain, (![A_97, B_98]: (r2_hidden(A_97, '#skF_3') | ~r2_hidden(B_98, k11_relat_1('#skF_4', A_97)))), inference(resolution, [status(thm)], [c_176, c_6])).
% 12.44/5.57  tff(c_7328, plain, (![A_1116, B_1117]: (~v1_relat_1('#skF_4') | r2_hidden('#skF_1'(A_1116, B_1117, '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1(A_1116, B_1117, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_1116, B_1117))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1116, B_1117))))), inference(resolution, [status(thm)], [c_7249, c_193])).
% 12.44/5.57  tff(c_7391, plain, (![A_1119, B_1120]: (r2_hidden('#skF_1'(A_1119, B_1120, '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1(A_1119, B_1120, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_1119, B_1120))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1119, B_1120))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_7328])).
% 12.44/5.57  tff(c_7394, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_38, c_7391])).
% 12.44/5.57  tff(c_7397, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7394])).
% 12.44/5.57  tff(c_7398, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_7397])).
% 12.44/5.57  tff(c_36, plain, (![D_48]: (k11_relat_1('#skF_5', D_48)=k11_relat_1('#skF_4', D_48) | ~r2_hidden(D_48, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.44/5.57  tff(c_7405, plain, (k11_relat_1('#skF_5', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))=k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_7398, c_36])).
% 12.44/5.57  tff(c_1425, plain, (![A_373, B_374, C_375, D_376]: (r2_hidden('#skF_2'(A_373, B_374, C_375, D_376), k11_relat_1(D_376, '#skF_1'(A_373, B_374, C_375, D_376))) | ~v1_relat_1(D_376) | r2_hidden(k4_tarski('#skF_1'(A_373, B_374, C_375, D_376), '#skF_2'(A_373, B_374, C_375, D_376)), C_375) | r2_relset_1(A_373, B_374, C_375, D_376) | ~m1_subset_1(D_376, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))))), inference(resolution, [status(thm)], [c_657, c_16])).
% 12.44/5.57  tff(c_11852, plain, (![A_1531, B_1532, C_1533, D_1534]: (r2_hidden('#skF_2'(A_1531, B_1532, C_1533, D_1534), k11_relat_1(C_1533, '#skF_1'(A_1531, B_1532, C_1533, D_1534))) | ~v1_relat_1(C_1533) | r2_hidden('#skF_2'(A_1531, B_1532, C_1533, D_1534), k11_relat_1(D_1534, '#skF_1'(A_1531, B_1532, C_1533, D_1534))) | ~v1_relat_1(D_1534) | r2_relset_1(A_1531, B_1532, C_1533, D_1534) | ~m1_subset_1(D_1534, k1_zfmisc_1(k2_zfmisc_1(A_1531, B_1532))) | ~m1_subset_1(C_1533, k1_zfmisc_1(k2_zfmisc_1(A_1531, B_1532))))), inference(resolution, [status(thm)], [c_1425, c_16])).
% 12.44/5.57  tff(c_12053, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_4') | r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7405, c_11852])).
% 12.44/5.57  tff(c_12129, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_51, c_54, c_12053])).
% 12.44/5.57  tff(c_12130, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_34, c_12129])).
% 12.44/5.57  tff(c_14, plain, (![A_14, B_15, C_16]: (r2_hidden(k4_tarski(A_14, B_15), C_16) | ~r2_hidden(B_15, k11_relat_1(C_16, A_14)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.44/5.57  tff(c_500, plain, (![A_211, B_212, C_213, D_214]: (~r2_hidden(k4_tarski('#skF_1'(A_211, B_212, C_213, D_214), '#skF_2'(A_211, B_212, C_213, D_214)), D_214) | ~r2_hidden(k4_tarski('#skF_1'(A_211, B_212, C_213, D_214), '#skF_2'(A_211, B_212, C_213, D_214)), C_213) | r2_relset_1(A_211, B_212, C_213, D_214) | ~m1_subset_1(D_214, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.44/5.57  tff(c_1307, plain, (![A_334, B_335, C_336, C_337]: (~r2_hidden(k4_tarski('#skF_1'(A_334, B_335, C_336, C_337), '#skF_2'(A_334, B_335, C_336, C_337)), C_336) | r2_relset_1(A_334, B_335, C_336, C_337) | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))) | ~r2_hidden('#skF_2'(A_334, B_335, C_336, C_337), k11_relat_1(C_337, '#skF_1'(A_334, B_335, C_336, C_337))) | ~v1_relat_1(C_337))), inference(resolution, [status(thm)], [c_14, c_500])).
% 12.44/5.57  tff(c_13230, plain, (![A_1591, B_1592, C_1593, C_1594]: (r2_relset_1(A_1591, B_1592, C_1593, C_1594) | ~m1_subset_1(C_1594, k1_zfmisc_1(k2_zfmisc_1(A_1591, B_1592))) | ~m1_subset_1(C_1593, k1_zfmisc_1(k2_zfmisc_1(A_1591, B_1592))) | ~r2_hidden('#skF_2'(A_1591, B_1592, C_1593, C_1594), k11_relat_1(C_1594, '#skF_1'(A_1591, B_1592, C_1593, C_1594))) | ~v1_relat_1(C_1594) | ~r2_hidden('#skF_2'(A_1591, B_1592, C_1593, C_1594), k11_relat_1(C_1593, '#skF_1'(A_1591, B_1592, C_1593, C_1594))) | ~v1_relat_1(C_1593))), inference(resolution, [status(thm)], [c_14, c_1307])).
% 12.44/5.57  tff(c_13255, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7405, c_13230])).
% 12.44/5.57  tff(c_13327, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_12130, c_51, c_12130, c_40, c_38, c_13255])).
% 12.44/5.57  tff(c_13329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_13327])).
% 12.44/5.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.44/5.57  
% 12.44/5.57  Inference rules
% 12.44/5.57  ----------------------
% 12.44/5.57  #Ref     : 0
% 12.44/5.57  #Sup     : 2701
% 12.44/5.57  #Fact    : 12
% 12.44/5.57  #Define  : 0
% 12.44/5.57  #Split   : 10
% 12.44/5.57  #Chain   : 0
% 12.44/5.57  #Close   : 0
% 12.44/5.57  
% 12.44/5.57  Ordering : KBO
% 12.44/5.57  
% 12.44/5.57  Simplification rules
% 12.44/5.57  ----------------------
% 12.44/5.57  #Subsume      : 433
% 12.44/5.57  #Demod        : 601
% 12.44/5.57  #Tautology    : 146
% 12.44/5.57  #SimpNegUnit  : 27
% 12.44/5.57  #BackRed      : 0
% 12.44/5.57  
% 12.44/5.57  #Partial instantiations: 0
% 12.44/5.57  #Strategies tried      : 1
% 12.44/5.57  
% 12.44/5.57  Timing (in seconds)
% 12.44/5.57  ----------------------
% 12.44/5.57  Preprocessing        : 0.30
% 12.44/5.57  Parsing              : 0.16
% 12.44/5.57  CNF conversion       : 0.03
% 12.44/5.57  Main loop            : 4.48
% 12.44/5.57  Inferencing          : 0.97
% 12.44/5.57  Reduction            : 0.80
% 12.44/5.57  Demodulation         : 0.49
% 12.44/5.57  BG Simplification    : 0.09
% 12.44/5.57  Subsumption          : 2.40
% 12.44/5.57  Abstraction          : 0.13
% 12.44/5.57  MUC search           : 0.00
% 12.44/5.57  Cooper               : 0.00
% 12.44/5.57  Total                : 4.82
% 12.44/5.57  Index Insertion      : 0.00
% 12.44/5.57  Index Deletion       : 0.00
% 12.44/5.57  Index Matching       : 0.00
% 12.44/5.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
