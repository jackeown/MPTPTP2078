%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:39 EST 2020

% Result     : Theorem 10.58s
% Output     : CNFRefutation 10.70s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 211 expanded)
%              Number of leaves         :   22 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  153 ( 695 expanded)
%              Number of equality atoms :    3 (  39 expanded)
%              Maximal formula depth    :   13 (   6 average)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ! [D] :
                  ( r2_hidden(D,A)
                 => k11_relat_1(B,D) = k11_relat_1(C,D) )
             => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_39,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_39])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_39])).

tff(c_444,plain,(
    ! [A_214,B_215,C_216,D_217] :
      ( r2_hidden(k4_tarski('#skF_1'(A_214,B_215,C_216,D_217),'#skF_2'(A_214,B_215,C_216,D_217)),C_216)
      | r2_hidden(k4_tarski('#skF_1'(A_214,B_215,C_216,D_217),'#skF_2'(A_214,B_215,C_216,D_217)),D_217)
      | r2_relset_1(A_214,B_215,C_216,D_217)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215)))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2283,plain,(
    ! [A_420,B_419,C_418,D_421,A_422] :
      ( r2_hidden(k4_tarski('#skF_1'(A_422,B_419,C_418,D_421),'#skF_2'(A_422,B_419,C_418,D_421)),A_420)
      | ~ m1_subset_1(D_421,k1_zfmisc_1(A_420))
      | r2_hidden(k4_tarski('#skF_1'(A_422,B_419,C_418,D_421),'#skF_2'(A_422,B_419,C_418,D_421)),C_418)
      | r2_relset_1(A_422,B_419,C_418,D_421)
      | ~ m1_subset_1(D_421,k1_zfmisc_1(k2_zfmisc_1(A_422,B_419)))
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(A_422,B_419))) ) ),
    inference(resolution,[status(thm)],[c_444,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6600,plain,(
    ! [C_941,A_937,D_939,C_942,D_938,B_940] :
      ( r2_hidden('#skF_1'(A_937,B_940,C_941,D_938),C_942)
      | ~ m1_subset_1(D_938,k1_zfmisc_1(k2_zfmisc_1(C_942,D_939)))
      | r2_hidden(k4_tarski('#skF_1'(A_937,B_940,C_941,D_938),'#skF_2'(A_937,B_940,C_941,D_938)),C_941)
      | r2_relset_1(A_937,B_940,C_941,D_938)
      | ~ m1_subset_1(D_938,k1_zfmisc_1(k2_zfmisc_1(A_937,B_940)))
      | ~ m1_subset_1(C_941,k1_zfmisc_1(k2_zfmisc_1(A_937,B_940))) ) ),
    inference(resolution,[status(thm)],[c_2283,c_6])).

tff(c_6605,plain,(
    ! [A_937,B_940,C_941] :
      ( r2_hidden('#skF_1'(A_937,B_940,C_941,'#skF_5'),'#skF_3')
      | r2_hidden(k4_tarski('#skF_1'(A_937,B_940,C_941,'#skF_5'),'#skF_2'(A_937,B_940,C_941,'#skF_5')),C_941)
      | r2_relset_1(A_937,B_940,C_941,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_937,B_940)))
      | ~ m1_subset_1(C_941,k1_zfmisc_1(k2_zfmisc_1(A_937,B_940))) ) ),
    inference(resolution,[status(thm)],[c_36,c_6600])).

tff(c_3252,plain,(
    ! [D_489,A_488,C_486,B_487,A_490] :
      ( r2_hidden(k4_tarski('#skF_1'(A_490,B_487,C_486,D_489),'#skF_2'(A_490,B_487,C_486,D_489)),A_488)
      | ~ m1_subset_1(C_486,k1_zfmisc_1(A_488))
      | r2_hidden(k4_tarski('#skF_1'(A_490,B_487,C_486,D_489),'#skF_2'(A_490,B_487,C_486,D_489)),D_489)
      | r2_relset_1(A_490,B_487,C_486,D_489)
      | ~ m1_subset_1(D_489,k1_zfmisc_1(k2_zfmisc_1(A_490,B_487)))
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1(A_490,B_487))) ) ),
    inference(resolution,[status(thm)],[c_444,c_8])).

tff(c_6912,plain,(
    ! [D_951,C_953,A_954,B_952,C_955,D_950] :
      ( r2_hidden('#skF_1'(A_954,B_952,C_953,D_950),C_955)
      | ~ m1_subset_1(C_953,k1_zfmisc_1(k2_zfmisc_1(C_955,D_951)))
      | r2_hidden(k4_tarski('#skF_1'(A_954,B_952,C_953,D_950),'#skF_2'(A_954,B_952,C_953,D_950)),D_950)
      | r2_relset_1(A_954,B_952,C_953,D_950)
      | ~ m1_subset_1(D_950,k1_zfmisc_1(k2_zfmisc_1(A_954,B_952)))
      | ~ m1_subset_1(C_953,k1_zfmisc_1(k2_zfmisc_1(A_954,B_952))) ) ),
    inference(resolution,[status(thm)],[c_3252,c_6])).

tff(c_7594,plain,(
    ! [A_1056,B_1057,D_1058] :
      ( r2_hidden('#skF_1'(A_1056,B_1057,'#skF_4',D_1058),'#skF_3')
      | r2_hidden(k4_tarski('#skF_1'(A_1056,B_1057,'#skF_4',D_1058),'#skF_2'(A_1056,B_1057,'#skF_4',D_1058)),D_1058)
      | r2_relset_1(A_1056,B_1057,'#skF_4',D_1058)
      | ~ m1_subset_1(D_1058,k1_zfmisc_1(k2_zfmisc_1(A_1056,B_1057)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1056,B_1057))) ) ),
    inference(resolution,[status(thm)],[c_38,c_6912])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17,D_31] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_15,B_16,C_17,D_31),'#skF_2'(A_15,B_16,C_17,D_31)),D_31)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_15,B_16,C_17,D_31),'#skF_2'(A_15,B_16,C_17,D_31)),C_17)
      | r2_relset_1(A_15,B_16,C_17,D_31)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8314,plain,(
    ! [A_1100,B_1101,D_1102] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1100,B_1101,'#skF_4',D_1102),'#skF_2'(A_1100,B_1101,'#skF_4',D_1102)),'#skF_4')
      | r2_hidden('#skF_1'(A_1100,B_1101,'#skF_4',D_1102),'#skF_3')
      | r2_relset_1(A_1100,B_1101,'#skF_4',D_1102)
      | ~ m1_subset_1(D_1102,k1_zfmisc_1(k2_zfmisc_1(A_1100,B_1101)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1100,B_1101))) ) ),
    inference(resolution,[status(thm)],[c_7594,c_20])).

tff(c_8427,plain,(
    ! [A_1103,B_1104] :
      ( r2_hidden('#skF_1'(A_1103,B_1104,'#skF_4','#skF_5'),'#skF_3')
      | r2_relset_1(A_1103,B_1104,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_1103,B_1104)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1103,B_1104))) ) ),
    inference(resolution,[status(thm)],[c_6605,c_8314])).

tff(c_8430,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_36,c_8427])).

tff(c_8433,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8430])).

tff(c_8434,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8433])).

tff(c_34,plain,(
    ! [D_46] :
      ( k11_relat_1('#skF_5',D_46) = k11_relat_1('#skF_4',D_46)
      | ~ r2_hidden(D_46,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8441,plain,(
    k11_relat_1('#skF_5','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')) = k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_8434,c_34])).

tff(c_12,plain,(
    ! [B_10,C_11,A_9] :
      ( r2_hidden(B_10,k11_relat_1(C_11,A_9))
      | ~ r2_hidden(k4_tarski(A_9,B_10),C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1406,plain,(
    ! [A_330,B_331,C_332,D_333] :
      ( r2_hidden('#skF_2'(A_330,B_331,C_332,D_333),k11_relat_1(C_332,'#skF_1'(A_330,B_331,C_332,D_333)))
      | ~ v1_relat_1(C_332)
      | r2_hidden(k4_tarski('#skF_1'(A_330,B_331,C_332,D_333),'#skF_2'(A_330,B_331,C_332,D_333)),D_333)
      | r2_relset_1(A_330,B_331,C_332,D_333)
      | ~ m1_subset_1(D_333,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331))) ) ),
    inference(resolution,[status(thm)],[c_444,c_12])).

tff(c_1644,plain,(
    ! [A_330,B_331,C_332,D_333] :
      ( r2_hidden('#skF_2'(A_330,B_331,C_332,D_333),k11_relat_1(D_333,'#skF_1'(A_330,B_331,C_332,D_333)))
      | ~ v1_relat_1(D_333)
      | r2_hidden('#skF_2'(A_330,B_331,C_332,D_333),k11_relat_1(C_332,'#skF_1'(A_330,B_331,C_332,D_333)))
      | ~ v1_relat_1(C_332)
      | r2_relset_1(A_330,B_331,C_332,D_333)
      | ~ m1_subset_1(D_333,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331))) ) ),
    inference(resolution,[status(thm)],[c_1406,c_12])).

tff(c_8835,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_4')
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8441,c_1644])).

tff(c_8991,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_47,c_46,c_8835])).

tff(c_8992,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8991])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden(k4_tarski(A_9,B_10),C_11)
      | ~ r2_hidden(B_10,k11_relat_1(C_11,A_9))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_330,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_165,B_166,C_167,D_168),'#skF_2'(A_165,B_166,C_167,D_168)),D_168)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_165,B_166,C_167,D_168),'#skF_2'(A_165,B_166,C_167,D_168)),C_167)
      | r2_relset_1(A_165,B_166,C_167,D_168)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2060,plain,(
    ! [A_373,B_374,C_375,C_376] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_373,B_374,C_375,C_376),'#skF_2'(A_373,B_374,C_375,C_376)),C_375)
      | r2_relset_1(A_373,B_374,C_375,C_376)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374)))
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374)))
      | ~ r2_hidden('#skF_2'(A_373,B_374,C_375,C_376),k11_relat_1(C_376,'#skF_1'(A_373,B_374,C_375,C_376)))
      | ~ v1_relat_1(C_376) ) ),
    inference(resolution,[status(thm)],[c_10,c_330])).

tff(c_11446,plain,(
    ! [A_1279,B_1280,C_1281,C_1282] :
      ( r2_relset_1(A_1279,B_1280,C_1281,C_1282)
      | ~ m1_subset_1(C_1282,k1_zfmisc_1(k2_zfmisc_1(A_1279,B_1280)))
      | ~ m1_subset_1(C_1281,k1_zfmisc_1(k2_zfmisc_1(A_1279,B_1280)))
      | ~ r2_hidden('#skF_2'(A_1279,B_1280,C_1281,C_1282),k11_relat_1(C_1282,'#skF_1'(A_1279,B_1280,C_1281,C_1282)))
      | ~ v1_relat_1(C_1282)
      | ~ r2_hidden('#skF_2'(A_1279,B_1280,C_1281,C_1282),k11_relat_1(C_1281,'#skF_1'(A_1279,B_1280,C_1281,C_1282)))
      | ~ v1_relat_1(C_1281) ) ),
    inference(resolution,[status(thm)],[c_10,c_2060])).

tff(c_11465,plain,
    ( r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4','#skF_5'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8441,c_11446])).

tff(c_11517,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_8992,c_46,c_8992,c_38,c_36,c_11465])).

tff(c_11519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_11517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:22:20 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.58/4.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.58/4.56  
% 10.58/4.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.58/4.57  %$ r2_relset_1 > r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.58/4.57  
% 10.58/4.57  %Foreground sorts:
% 10.58/4.57  
% 10.58/4.57  
% 10.58/4.57  %Background operators:
% 10.58/4.57  
% 10.58/4.57  
% 10.58/4.57  %Foreground operators:
% 10.58/4.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.58/4.57  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.58/4.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.58/4.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.58/4.57  tff('#skF_5', type, '#skF_5': $i).
% 10.58/4.57  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 10.58/4.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 10.58/4.57  tff('#skF_3', type, '#skF_3': $i).
% 10.58/4.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.58/4.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.58/4.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.58/4.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.58/4.57  tff('#skF_4', type, '#skF_4': $i).
% 10.58/4.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.58/4.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 10.58/4.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.58/4.57  
% 10.70/4.58  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relset_1)).
% 10.70/4.58  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.70/4.58  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (r2_hidden(k4_tarski(E, F), C) <=> r2_hidden(k4_tarski(E, F), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relset_1)).
% 10.70/4.58  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 10.70/4.58  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 10.70/4.58  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 10.70/4.58  tff(c_32, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.70/4.58  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.70/4.58  tff(c_39, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.70/4.58  tff(c_47, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_39])).
% 10.70/4.58  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.70/4.59  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_39])).
% 10.70/4.59  tff(c_444, plain, (![A_214, B_215, C_216, D_217]: (r2_hidden(k4_tarski('#skF_1'(A_214, B_215, C_216, D_217), '#skF_2'(A_214, B_215, C_216, D_217)), C_216) | r2_hidden(k4_tarski('#skF_1'(A_214, B_215, C_216, D_217), '#skF_2'(A_214, B_215, C_216, D_217)), D_217) | r2_relset_1(A_214, B_215, C_216, D_217) | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.70/4.59  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.70/4.59  tff(c_2283, plain, (![A_420, B_419, C_418, D_421, A_422]: (r2_hidden(k4_tarski('#skF_1'(A_422, B_419, C_418, D_421), '#skF_2'(A_422, B_419, C_418, D_421)), A_420) | ~m1_subset_1(D_421, k1_zfmisc_1(A_420)) | r2_hidden(k4_tarski('#skF_1'(A_422, B_419, C_418, D_421), '#skF_2'(A_422, B_419, C_418, D_421)), C_418) | r2_relset_1(A_422, B_419, C_418, D_421) | ~m1_subset_1(D_421, k1_zfmisc_1(k2_zfmisc_1(A_422, B_419))) | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(A_422, B_419))))), inference(resolution, [status(thm)], [c_444, c_8])).
% 10.70/4.59  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.70/4.59  tff(c_6600, plain, (![C_941, A_937, D_939, C_942, D_938, B_940]: (r2_hidden('#skF_1'(A_937, B_940, C_941, D_938), C_942) | ~m1_subset_1(D_938, k1_zfmisc_1(k2_zfmisc_1(C_942, D_939))) | r2_hidden(k4_tarski('#skF_1'(A_937, B_940, C_941, D_938), '#skF_2'(A_937, B_940, C_941, D_938)), C_941) | r2_relset_1(A_937, B_940, C_941, D_938) | ~m1_subset_1(D_938, k1_zfmisc_1(k2_zfmisc_1(A_937, B_940))) | ~m1_subset_1(C_941, k1_zfmisc_1(k2_zfmisc_1(A_937, B_940))))), inference(resolution, [status(thm)], [c_2283, c_6])).
% 10.70/4.59  tff(c_6605, plain, (![A_937, B_940, C_941]: (r2_hidden('#skF_1'(A_937, B_940, C_941, '#skF_5'), '#skF_3') | r2_hidden(k4_tarski('#skF_1'(A_937, B_940, C_941, '#skF_5'), '#skF_2'(A_937, B_940, C_941, '#skF_5')), C_941) | r2_relset_1(A_937, B_940, C_941, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_937, B_940))) | ~m1_subset_1(C_941, k1_zfmisc_1(k2_zfmisc_1(A_937, B_940))))), inference(resolution, [status(thm)], [c_36, c_6600])).
% 10.70/4.59  tff(c_3252, plain, (![D_489, A_488, C_486, B_487, A_490]: (r2_hidden(k4_tarski('#skF_1'(A_490, B_487, C_486, D_489), '#skF_2'(A_490, B_487, C_486, D_489)), A_488) | ~m1_subset_1(C_486, k1_zfmisc_1(A_488)) | r2_hidden(k4_tarski('#skF_1'(A_490, B_487, C_486, D_489), '#skF_2'(A_490, B_487, C_486, D_489)), D_489) | r2_relset_1(A_490, B_487, C_486, D_489) | ~m1_subset_1(D_489, k1_zfmisc_1(k2_zfmisc_1(A_490, B_487))) | ~m1_subset_1(C_486, k1_zfmisc_1(k2_zfmisc_1(A_490, B_487))))), inference(resolution, [status(thm)], [c_444, c_8])).
% 10.70/4.59  tff(c_6912, plain, (![D_951, C_953, A_954, B_952, C_955, D_950]: (r2_hidden('#skF_1'(A_954, B_952, C_953, D_950), C_955) | ~m1_subset_1(C_953, k1_zfmisc_1(k2_zfmisc_1(C_955, D_951))) | r2_hidden(k4_tarski('#skF_1'(A_954, B_952, C_953, D_950), '#skF_2'(A_954, B_952, C_953, D_950)), D_950) | r2_relset_1(A_954, B_952, C_953, D_950) | ~m1_subset_1(D_950, k1_zfmisc_1(k2_zfmisc_1(A_954, B_952))) | ~m1_subset_1(C_953, k1_zfmisc_1(k2_zfmisc_1(A_954, B_952))))), inference(resolution, [status(thm)], [c_3252, c_6])).
% 10.70/4.59  tff(c_7594, plain, (![A_1056, B_1057, D_1058]: (r2_hidden('#skF_1'(A_1056, B_1057, '#skF_4', D_1058), '#skF_3') | r2_hidden(k4_tarski('#skF_1'(A_1056, B_1057, '#skF_4', D_1058), '#skF_2'(A_1056, B_1057, '#skF_4', D_1058)), D_1058) | r2_relset_1(A_1056, B_1057, '#skF_4', D_1058) | ~m1_subset_1(D_1058, k1_zfmisc_1(k2_zfmisc_1(A_1056, B_1057))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1056, B_1057))))), inference(resolution, [status(thm)], [c_38, c_6912])).
% 10.70/4.59  tff(c_20, plain, (![A_15, B_16, C_17, D_31]: (~r2_hidden(k4_tarski('#skF_1'(A_15, B_16, C_17, D_31), '#skF_2'(A_15, B_16, C_17, D_31)), D_31) | ~r2_hidden(k4_tarski('#skF_1'(A_15, B_16, C_17, D_31), '#skF_2'(A_15, B_16, C_17, D_31)), C_17) | r2_relset_1(A_15, B_16, C_17, D_31) | ~m1_subset_1(D_31, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.70/4.59  tff(c_8314, plain, (![A_1100, B_1101, D_1102]: (~r2_hidden(k4_tarski('#skF_1'(A_1100, B_1101, '#skF_4', D_1102), '#skF_2'(A_1100, B_1101, '#skF_4', D_1102)), '#skF_4') | r2_hidden('#skF_1'(A_1100, B_1101, '#skF_4', D_1102), '#skF_3') | r2_relset_1(A_1100, B_1101, '#skF_4', D_1102) | ~m1_subset_1(D_1102, k1_zfmisc_1(k2_zfmisc_1(A_1100, B_1101))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1100, B_1101))))), inference(resolution, [status(thm)], [c_7594, c_20])).
% 10.70/4.59  tff(c_8427, plain, (![A_1103, B_1104]: (r2_hidden('#skF_1'(A_1103, B_1104, '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1(A_1103, B_1104, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_1103, B_1104))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1103, B_1104))))), inference(resolution, [status(thm)], [c_6605, c_8314])).
% 10.70/4.59  tff(c_8430, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_36, c_8427])).
% 10.70/4.59  tff(c_8433, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8430])).
% 10.70/4.59  tff(c_8434, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_8433])).
% 10.70/4.59  tff(c_34, plain, (![D_46]: (k11_relat_1('#skF_5', D_46)=k11_relat_1('#skF_4', D_46) | ~r2_hidden(D_46, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.70/4.59  tff(c_8441, plain, (k11_relat_1('#skF_5', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))=k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_8434, c_34])).
% 10.70/4.59  tff(c_12, plain, (![B_10, C_11, A_9]: (r2_hidden(B_10, k11_relat_1(C_11, A_9)) | ~r2_hidden(k4_tarski(A_9, B_10), C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.70/4.59  tff(c_1406, plain, (![A_330, B_331, C_332, D_333]: (r2_hidden('#skF_2'(A_330, B_331, C_332, D_333), k11_relat_1(C_332, '#skF_1'(A_330, B_331, C_332, D_333))) | ~v1_relat_1(C_332) | r2_hidden(k4_tarski('#skF_1'(A_330, B_331, C_332, D_333), '#skF_2'(A_330, B_331, C_332, D_333)), D_333) | r2_relset_1(A_330, B_331, C_332, D_333) | ~m1_subset_1(D_333, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))))), inference(resolution, [status(thm)], [c_444, c_12])).
% 10.70/4.59  tff(c_1644, plain, (![A_330, B_331, C_332, D_333]: (r2_hidden('#skF_2'(A_330, B_331, C_332, D_333), k11_relat_1(D_333, '#skF_1'(A_330, B_331, C_332, D_333))) | ~v1_relat_1(D_333) | r2_hidden('#skF_2'(A_330, B_331, C_332, D_333), k11_relat_1(C_332, '#skF_1'(A_330, B_331, C_332, D_333))) | ~v1_relat_1(C_332) | r2_relset_1(A_330, B_331, C_332, D_333) | ~m1_subset_1(D_333, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))))), inference(resolution, [status(thm)], [c_1406, c_12])).
% 10.70/4.59  tff(c_8835, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_4') | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8441, c_1644])).
% 10.70/4.59  tff(c_8991, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_47, c_46, c_8835])).
% 10.70/4.59  tff(c_8992, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_32, c_8991])).
% 10.70/4.59  tff(c_10, plain, (![A_9, B_10, C_11]: (r2_hidden(k4_tarski(A_9, B_10), C_11) | ~r2_hidden(B_10, k11_relat_1(C_11, A_9)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.70/4.59  tff(c_330, plain, (![A_165, B_166, C_167, D_168]: (~r2_hidden(k4_tarski('#skF_1'(A_165, B_166, C_167, D_168), '#skF_2'(A_165, B_166, C_167, D_168)), D_168) | ~r2_hidden(k4_tarski('#skF_1'(A_165, B_166, C_167, D_168), '#skF_2'(A_165, B_166, C_167, D_168)), C_167) | r2_relset_1(A_165, B_166, C_167, D_168) | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.70/4.59  tff(c_2060, plain, (![A_373, B_374, C_375, C_376]: (~r2_hidden(k4_tarski('#skF_1'(A_373, B_374, C_375, C_376), '#skF_2'(A_373, B_374, C_375, C_376)), C_375) | r2_relset_1(A_373, B_374, C_375, C_376) | ~m1_subset_1(C_376, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))) | ~r2_hidden('#skF_2'(A_373, B_374, C_375, C_376), k11_relat_1(C_376, '#skF_1'(A_373, B_374, C_375, C_376))) | ~v1_relat_1(C_376))), inference(resolution, [status(thm)], [c_10, c_330])).
% 10.70/4.59  tff(c_11446, plain, (![A_1279, B_1280, C_1281, C_1282]: (r2_relset_1(A_1279, B_1280, C_1281, C_1282) | ~m1_subset_1(C_1282, k1_zfmisc_1(k2_zfmisc_1(A_1279, B_1280))) | ~m1_subset_1(C_1281, k1_zfmisc_1(k2_zfmisc_1(A_1279, B_1280))) | ~r2_hidden('#skF_2'(A_1279, B_1280, C_1281, C_1282), k11_relat_1(C_1282, '#skF_1'(A_1279, B_1280, C_1281, C_1282))) | ~v1_relat_1(C_1282) | ~r2_hidden('#skF_2'(A_1279, B_1280, C_1281, C_1282), k11_relat_1(C_1281, '#skF_1'(A_1279, B_1280, C_1281, C_1282))) | ~v1_relat_1(C_1281))), inference(resolution, [status(thm)], [c_10, c_2060])).
% 10.70/4.59  tff(c_11465, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8441, c_11446])).
% 10.70/4.59  tff(c_11517, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_8992, c_46, c_8992, c_38, c_36, c_11465])).
% 10.70/4.59  tff(c_11519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_11517])).
% 10.70/4.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.70/4.59  
% 10.70/4.59  Inference rules
% 10.70/4.59  ----------------------
% 10.70/4.59  #Ref     : 0
% 10.70/4.59  #Sup     : 2371
% 10.70/4.59  #Fact    : 12
% 10.70/4.59  #Define  : 0
% 10.70/4.59  #Split   : 11
% 10.70/4.59  #Chain   : 0
% 10.70/4.59  #Close   : 0
% 10.70/4.59  
% 10.70/4.59  Ordering : KBO
% 10.70/4.59  
% 10.70/4.59  Simplification rules
% 10.70/4.59  ----------------------
% 10.70/4.59  #Subsume      : 362
% 10.70/4.59  #Demod        : 489
% 10.70/4.59  #Tautology    : 155
% 10.70/4.59  #SimpNegUnit  : 25
% 10.70/4.59  #BackRed      : 0
% 10.70/4.59  
% 10.70/4.59  #Partial instantiations: 0
% 10.70/4.59  #Strategies tried      : 1
% 10.70/4.59  
% 10.70/4.59  Timing (in seconds)
% 10.70/4.59  ----------------------
% 10.70/4.59  Preprocessing        : 0.30
% 10.70/4.59  Parsing              : 0.16
% 10.70/4.59  CNF conversion       : 0.02
% 10.70/4.59  Main loop            : 3.53
% 10.70/4.59  Inferencing          : 0.79
% 10.70/4.59  Reduction            : 0.61
% 10.70/4.59  Demodulation         : 0.39
% 10.70/4.59  BG Simplification    : 0.08
% 10.70/4.59  Subsumption          : 1.87
% 10.70/4.59  Abstraction          : 0.11
% 10.70/4.59  MUC search           : 0.00
% 10.70/4.59  Cooper               : 0.00
% 10.70/4.59  Total                : 3.87
% 10.70/4.59  Index Insertion      : 0.00
% 10.70/4.59  Index Deletion       : 0.00
% 10.70/4.59  Index Matching       : 0.00
% 10.70/4.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
