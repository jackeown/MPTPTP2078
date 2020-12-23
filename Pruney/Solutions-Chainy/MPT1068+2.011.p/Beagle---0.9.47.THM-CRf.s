%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:42 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 268 expanded)
%              Number of leaves         :   37 ( 116 expanded)
%              Depth                    :   12
%              Number of atoms          :  193 (1143 expanded)
%              Number of equality atoms :   47 ( 248 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_relat_1(E)
            & v1_funct_1(E) )
         => ( r2_hidden(C,A)
           => ( B = k1_xboole_0
              | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_36,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_107,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_115,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_107])).

tff(c_40,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_202,plain,(
    ! [C_89,B_92,E_91,F_90,A_94,D_93] :
      ( k1_partfun1(A_94,B_92,C_89,D_93,E_91,F_90) = k5_relat_1(E_91,F_90)
      | ~ m1_subset_1(F_90,k1_zfmisc_1(k2_zfmisc_1(C_89,D_93)))
      | ~ v1_funct_1(F_90)
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_94,B_92)))
      | ~ v1_funct_1(E_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_206,plain,(
    ! [A_94,B_92,E_91] :
      ( k1_partfun1(A_94,B_92,'#skF_5','#skF_3',E_91,'#skF_7') = k5_relat_1(E_91,'#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_94,B_92)))
      | ~ v1_funct_1(E_91) ) ),
    inference(resolution,[status(thm)],[c_38,c_202])).

tff(c_802,plain,(
    ! [A_179,B_180,E_181] :
      ( k1_partfun1(A_179,B_180,'#skF_5','#skF_3',E_181,'#skF_7') = k5_relat_1(E_181,'#skF_7')
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_1(E_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_206])).

tff(c_805,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_802])).

tff(c_811,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_805])).

tff(c_34,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_871,plain,(
    ! [A_191,B_192,C_190,D_193,E_194] :
      ( k1_partfun1(A_191,B_192,B_192,C_190,D_193,E_194) = k8_funct_2(A_191,B_192,C_190,D_193,E_194)
      | k1_xboole_0 = B_192
      | ~ r1_tarski(k2_relset_1(A_191,B_192,D_193),k1_relset_1(B_192,C_190,E_194))
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(B_192,C_190)))
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1(D_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192)))
      | ~ v1_funct_2(D_193,A_191,B_192)
      | ~ v1_funct_1(D_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_874,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_871])).

tff(c_880,plain,
    ( k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_811,c_874])).

tff(c_882,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_880])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_886,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_882,c_12])).

tff(c_889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_886])).

tff(c_891,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_880])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_773,plain,(
    ! [E_177,A_176,B_175,C_178,D_174] :
      ( k1_funct_1(k5_relat_1(D_174,E_177),C_178) = k1_funct_1(E_177,k1_funct_1(D_174,C_178))
      | k1_xboole_0 = B_175
      | ~ r2_hidden(C_178,A_176)
      | ~ v1_funct_1(E_177)
      | ~ v1_relat_1(E_177)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_176,B_175)))
      | ~ v1_funct_2(D_174,A_176,B_175)
      | ~ v1_funct_1(D_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_918,plain,(
    ! [D_206,E_207,A_208,B_209] :
      ( k1_funct_1(k5_relat_1(D_206,E_207),'#skF_1'(A_208)) = k1_funct_1(E_207,k1_funct_1(D_206,'#skF_1'(A_208)))
      | k1_xboole_0 = B_209
      | ~ v1_funct_1(E_207)
      | ~ v1_relat_1(E_207)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209)))
      | ~ v1_funct_2(D_206,A_208,B_209)
      | ~ v1_funct_1(D_206)
      | v1_xboole_0(A_208) ) ),
    inference(resolution,[status(thm)],[c_4,c_773])).

tff(c_920,plain,(
    ! [E_207] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_207),'#skF_1'('#skF_4')) = k1_funct_1(E_207,k1_funct_1('#skF_6','#skF_1'('#skF_4')))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_207)
      | ~ v1_relat_1(E_207)
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_918])).

tff(c_925,plain,(
    ! [E_207] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_207),'#skF_1'('#skF_4')) = k1_funct_1(E_207,k1_funct_1('#skF_6','#skF_1'('#skF_4')))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_207)
      | ~ v1_relat_1(E_207)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_920])).

tff(c_926,plain,(
    ! [E_207] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_207),'#skF_1'('#skF_4')) = k1_funct_1(E_207,k1_funct_1('#skF_6','#skF_1'('#skF_4')))
      | ~ v1_funct_1(E_207)
      | ~ v1_relat_1(E_207)
      | v1_xboole_0('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_891,c_925])).

tff(c_944,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_926])).

tff(c_64,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_52,B_53] :
      ( ~ v1_xboole_0(A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_69,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_69,c_14])).

tff(c_90,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ v1_xboole_0(B_60)
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_68,c_80])).

tff(c_93,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_12,c_90])).

tff(c_947,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_944,c_93])).

tff(c_953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_947])).

tff(c_955,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_931,plain,(
    ! [B_211,D_210,B_214,E_213,A_212] :
      ( k1_funct_1(k5_relat_1(D_210,E_213),A_212) = k1_funct_1(E_213,k1_funct_1(D_210,A_212))
      | k1_xboole_0 = B_214
      | ~ v1_funct_1(E_213)
      | ~ v1_relat_1(E_213)
      | ~ m1_subset_1(D_210,k1_zfmisc_1(k2_zfmisc_1(B_211,B_214)))
      | ~ v1_funct_2(D_210,B_211,B_214)
      | ~ v1_funct_1(D_210)
      | v1_xboole_0(B_211)
      | ~ m1_subset_1(A_212,B_211) ) ),
    inference(resolution,[status(thm)],[c_20,c_773])).

tff(c_933,plain,(
    ! [E_213,A_212] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_213),A_212) = k1_funct_1(E_213,k1_funct_1('#skF_6',A_212))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_213)
      | ~ v1_relat_1(E_213)
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_212,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_931])).

tff(c_938,plain,(
    ! [E_213,A_212] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_213),A_212) = k1_funct_1(E_213,k1_funct_1('#skF_6',A_212))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_213)
      | ~ v1_relat_1(E_213)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_212,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_933])).

tff(c_939,plain,(
    ! [E_213,A_212] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_213),A_212) = k1_funct_1(E_213,k1_funct_1('#skF_6',A_212))
      | ~ v1_funct_1(E_213)
      | ~ v1_relat_1(E_213)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_212,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_891,c_938])).

tff(c_967,plain,(
    ! [E_216,A_217] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_216),A_217) = k1_funct_1(E_216,k1_funct_1('#skF_6',A_217))
      | ~ v1_funct_1(E_216)
      | ~ v1_relat_1(E_216)
      | ~ m1_subset_1(A_217,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_955,c_939])).

tff(c_890,plain,(
    k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_880])).

tff(c_30,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_893,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_30])).

tff(c_977,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_967,c_893])).

tff(c_989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_115,c_40,c_977])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.56  
% 3.54/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.57  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 3.54/1.57  
% 3.54/1.57  %Foreground sorts:
% 3.54/1.57  
% 3.54/1.57  
% 3.54/1.57  %Background operators:
% 3.54/1.57  
% 3.54/1.57  
% 3.54/1.57  %Foreground operators:
% 3.54/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.54/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.54/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.54/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.54/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.57  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.54/1.57  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.54/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.54/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.54/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.54/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.57  
% 3.54/1.58  tff(f_124, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.54/1.58  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.54/1.58  tff(f_82, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.54/1.58  tff(f_72, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 3.54/1.58  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.54/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.54/1.58  tff(f_99, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 3.54/1.58  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.54/1.58  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.54/1.58  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.54/1.58  tff(c_36, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_107, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.54/1.58  tff(c_115, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_38, c_107])).
% 3.54/1.58  tff(c_40, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_48, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_202, plain, (![C_89, B_92, E_91, F_90, A_94, D_93]: (k1_partfun1(A_94, B_92, C_89, D_93, E_91, F_90)=k5_relat_1(E_91, F_90) | ~m1_subset_1(F_90, k1_zfmisc_1(k2_zfmisc_1(C_89, D_93))) | ~v1_funct_1(F_90) | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_94, B_92))) | ~v1_funct_1(E_91))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.54/1.58  tff(c_206, plain, (![A_94, B_92, E_91]: (k1_partfun1(A_94, B_92, '#skF_5', '#skF_3', E_91, '#skF_7')=k5_relat_1(E_91, '#skF_7') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_94, B_92))) | ~v1_funct_1(E_91))), inference(resolution, [status(thm)], [c_38, c_202])).
% 3.54/1.58  tff(c_802, plain, (![A_179, B_180, E_181]: (k1_partfun1(A_179, B_180, '#skF_5', '#skF_3', E_181, '#skF_7')=k5_relat_1(E_181, '#skF_7') | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_1(E_181))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_206])).
% 3.54/1.58  tff(c_805, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_802])).
% 3.54/1.58  tff(c_811, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_805])).
% 3.54/1.58  tff(c_34, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_871, plain, (![A_191, B_192, C_190, D_193, E_194]: (k1_partfun1(A_191, B_192, B_192, C_190, D_193, E_194)=k8_funct_2(A_191, B_192, C_190, D_193, E_194) | k1_xboole_0=B_192 | ~r1_tarski(k2_relset_1(A_191, B_192, D_193), k1_relset_1(B_192, C_190, E_194)) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(B_192, C_190))) | ~v1_funct_1(E_194) | ~m1_subset_1(D_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))) | ~v1_funct_2(D_193, A_191, B_192) | ~v1_funct_1(D_193))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.54/1.58  tff(c_874, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_871])).
% 3.54/1.58  tff(c_880, plain, (k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_811, c_874])).
% 3.54/1.58  tff(c_882, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_880])).
% 3.54/1.58  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.58  tff(c_886, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_882, c_12])).
% 3.54/1.58  tff(c_889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_886])).
% 3.54/1.58  tff(c_891, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_880])).
% 3.54/1.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.58  tff(c_773, plain, (![E_177, A_176, B_175, C_178, D_174]: (k1_funct_1(k5_relat_1(D_174, E_177), C_178)=k1_funct_1(E_177, k1_funct_1(D_174, C_178)) | k1_xboole_0=B_175 | ~r2_hidden(C_178, A_176) | ~v1_funct_1(E_177) | ~v1_relat_1(E_177) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_176, B_175))) | ~v1_funct_2(D_174, A_176, B_175) | ~v1_funct_1(D_174))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.54/1.58  tff(c_918, plain, (![D_206, E_207, A_208, B_209]: (k1_funct_1(k5_relat_1(D_206, E_207), '#skF_1'(A_208))=k1_funct_1(E_207, k1_funct_1(D_206, '#skF_1'(A_208))) | k1_xboole_0=B_209 | ~v1_funct_1(E_207) | ~v1_relat_1(E_207) | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))) | ~v1_funct_2(D_206, A_208, B_209) | ~v1_funct_1(D_206) | v1_xboole_0(A_208))), inference(resolution, [status(thm)], [c_4, c_773])).
% 3.54/1.58  tff(c_920, plain, (![E_207]: (k1_funct_1(k5_relat_1('#skF_6', E_207), '#skF_1'('#skF_4'))=k1_funct_1(E_207, k1_funct_1('#skF_6', '#skF_1'('#skF_4'))) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_207) | ~v1_relat_1(E_207) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_918])).
% 3.54/1.58  tff(c_925, plain, (![E_207]: (k1_funct_1(k5_relat_1('#skF_6', E_207), '#skF_1'('#skF_4'))=k1_funct_1(E_207, k1_funct_1('#skF_6', '#skF_1'('#skF_4'))) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_207) | ~v1_relat_1(E_207) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_920])).
% 3.54/1.58  tff(c_926, plain, (![E_207]: (k1_funct_1(k5_relat_1('#skF_6', E_207), '#skF_1'('#skF_4'))=k1_funct_1(E_207, k1_funct_1('#skF_6', '#skF_1'('#skF_4'))) | ~v1_funct_1(E_207) | ~v1_relat_1(E_207) | v1_xboole_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_891, c_925])).
% 3.54/1.58  tff(c_944, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_926])).
% 3.54/1.58  tff(c_64, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.54/1.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.58  tff(c_68, plain, (![A_52, B_53]: (~v1_xboole_0(A_52) | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_64, c_2])).
% 3.54/1.58  tff(c_69, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_64, c_2])).
% 3.54/1.58  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.54/1.58  tff(c_80, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_69, c_14])).
% 3.54/1.58  tff(c_90, plain, (![B_60, A_61]: (B_60=A_61 | ~v1_xboole_0(B_60) | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_68, c_80])).
% 3.54/1.58  tff(c_93, plain, (![A_61]: (k1_xboole_0=A_61 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_12, c_90])).
% 3.54/1.58  tff(c_947, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_944, c_93])).
% 3.54/1.58  tff(c_953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_947])).
% 3.54/1.58  tff(c_955, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_926])).
% 3.54/1.58  tff(c_20, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.54/1.58  tff(c_931, plain, (![B_211, D_210, B_214, E_213, A_212]: (k1_funct_1(k5_relat_1(D_210, E_213), A_212)=k1_funct_1(E_213, k1_funct_1(D_210, A_212)) | k1_xboole_0=B_214 | ~v1_funct_1(E_213) | ~v1_relat_1(E_213) | ~m1_subset_1(D_210, k1_zfmisc_1(k2_zfmisc_1(B_211, B_214))) | ~v1_funct_2(D_210, B_211, B_214) | ~v1_funct_1(D_210) | v1_xboole_0(B_211) | ~m1_subset_1(A_212, B_211))), inference(resolution, [status(thm)], [c_20, c_773])).
% 3.54/1.58  tff(c_933, plain, (![E_213, A_212]: (k1_funct_1(k5_relat_1('#skF_6', E_213), A_212)=k1_funct_1(E_213, k1_funct_1('#skF_6', A_212)) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_213) | ~v1_relat_1(E_213) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_212, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_931])).
% 3.54/1.58  tff(c_938, plain, (![E_213, A_212]: (k1_funct_1(k5_relat_1('#skF_6', E_213), A_212)=k1_funct_1(E_213, k1_funct_1('#skF_6', A_212)) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_213) | ~v1_relat_1(E_213) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_212, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_933])).
% 3.54/1.58  tff(c_939, plain, (![E_213, A_212]: (k1_funct_1(k5_relat_1('#skF_6', E_213), A_212)=k1_funct_1(E_213, k1_funct_1('#skF_6', A_212)) | ~v1_funct_1(E_213) | ~v1_relat_1(E_213) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_212, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_891, c_938])).
% 3.54/1.58  tff(c_967, plain, (![E_216, A_217]: (k1_funct_1(k5_relat_1('#skF_6', E_216), A_217)=k1_funct_1(E_216, k1_funct_1('#skF_6', A_217)) | ~v1_funct_1(E_216) | ~v1_relat_1(E_216) | ~m1_subset_1(A_217, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_955, c_939])).
% 3.54/1.58  tff(c_890, plain, (k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_880])).
% 3.54/1.58  tff(c_30, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_893, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_890, c_30])).
% 3.54/1.58  tff(c_977, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_967, c_893])).
% 3.54/1.58  tff(c_989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_115, c_40, c_977])).
% 3.54/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.58  
% 3.54/1.58  Inference rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Ref     : 0
% 3.54/1.58  #Sup     : 214
% 3.54/1.58  #Fact    : 0
% 3.54/1.58  #Define  : 0
% 3.54/1.58  #Split   : 13
% 3.54/1.58  #Chain   : 0
% 3.54/1.58  #Close   : 0
% 3.54/1.58  
% 3.54/1.58  Ordering : KBO
% 3.54/1.58  
% 3.54/1.58  Simplification rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Subsume      : 67
% 3.54/1.58  #Demod        : 92
% 3.54/1.58  #Tautology    : 44
% 3.54/1.58  #SimpNegUnit  : 13
% 3.54/1.58  #BackRed      : 34
% 3.54/1.58  
% 3.54/1.58  #Partial instantiations: 0
% 3.54/1.58  #Strategies tried      : 1
% 3.54/1.58  
% 3.54/1.58  Timing (in seconds)
% 3.54/1.58  ----------------------
% 3.54/1.59  Preprocessing        : 0.32
% 3.54/1.59  Parsing              : 0.17
% 3.54/1.59  CNF conversion       : 0.02
% 3.54/1.59  Main loop            : 0.47
% 3.54/1.59  Inferencing          : 0.16
% 3.54/1.59  Reduction            : 0.14
% 3.54/1.59  Demodulation         : 0.09
% 3.54/1.59  BG Simplification    : 0.02
% 3.54/1.59  Subsumption          : 0.12
% 3.54/1.59  Abstraction          : 0.02
% 3.54/1.59  MUC search           : 0.00
% 3.54/1.59  Cooper               : 0.00
% 3.54/1.59  Total                : 0.82
% 3.54/1.59  Index Insertion      : 0.00
% 3.54/1.59  Index Deletion       : 0.00
% 3.54/1.59  Index Matching       : 0.00
% 3.54/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
