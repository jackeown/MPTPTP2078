%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:55 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 289 expanded)
%              Number of leaves         :   43 ( 120 expanded)
%              Depth                    :   19
%              Number of atoms          :  213 ( 894 expanded)
%              Number of equality atoms :   43 ( 190 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_38,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C] :
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

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_38,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_151,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_158,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_151])).

tff(c_138,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_146,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_138])).

tff(c_36,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_160,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_36])).

tff(c_173,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_160])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_10,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_51])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_57,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_34])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_28,plain,(
    ! [C_29,B_28,D_37,E_41,A_27,F_43] :
      ( k1_funct_1(k8_funct_2(B_28,C_29,A_27,D_37,E_41),F_43) = k1_funct_1(E_41,k1_funct_1(D_37,F_43))
      | k1_xboole_0 = B_28
      | ~ r1_tarski(k2_relset_1(B_28,C_29,D_37),k1_relset_1(C_29,A_27,E_41))
      | ~ m1_subset_1(F_43,B_28)
      | ~ m1_subset_1(E_41,k1_zfmisc_1(k2_zfmisc_1(C_29,A_27)))
      | ~ v1_funct_1(E_41)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(B_28,C_29)))
      | ~ v1_funct_2(D_37,B_28,C_29)
      | ~ v1_funct_1(D_37)
      | v1_xboole_0(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_805,plain,(
    ! [B_210,C_207,F_209,E_208,A_211,D_206] :
      ( k1_funct_1(k8_funct_2(B_210,C_207,A_211,D_206,E_208),F_209) = k1_funct_1(E_208,k1_funct_1(D_206,F_209))
      | B_210 = '#skF_2'
      | ~ r1_tarski(k2_relset_1(B_210,C_207,D_206),k1_relset_1(C_207,A_211,E_208))
      | ~ m1_subset_1(F_209,B_210)
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(C_207,A_211)))
      | ~ v1_funct_1(E_208)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(B_210,C_207)))
      | ~ v1_funct_2(D_206,B_210,C_207)
      | ~ v1_funct_1(D_206)
      | v1_xboole_0(C_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_28])).

tff(c_807,plain,(
    ! [A_211,E_208,F_209] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_211,'#skF_6',E_208),F_209) = k1_funct_1(E_208,k1_funct_1('#skF_6',F_209))
      | '#skF_2' = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_211,E_208))
      | ~ m1_subset_1(F_209,'#skF_4')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_211)))
      | ~ v1_funct_1(E_208)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_805])).

tff(c_815,plain,(
    ! [A_211,E_208,F_209] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_211,'#skF_6',E_208),F_209) = k1_funct_1(E_208,k1_funct_1('#skF_6',F_209))
      | '#skF_2' = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_211,E_208))
      | ~ m1_subset_1(F_209,'#skF_4')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_211)))
      | ~ v1_funct_1(E_208)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_807])).

tff(c_849,plain,(
    ! [A_218,E_219,F_220] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_218,'#skF_6',E_219),F_220) = k1_funct_1(E_219,k1_funct_1('#skF_6',F_220))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_218,E_219))
      | ~ m1_subset_1(F_220,'#skF_4')
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_218)))
      | ~ v1_funct_1(E_219) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_57,c_815])).

tff(c_851,plain,(
    ! [F_220] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_220) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_220))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_220,'#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_849])).

tff(c_853,plain,(
    ! [F_220] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_220) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_220))
      | ~ m1_subset_1(F_220,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_173,c_851])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_104,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_96])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_69,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_69])).

tff(c_81,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_75])).

tff(c_89,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),A_69)
      | r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_69] : r1_tarski(A_69,A_69) ),
    inference(resolution,[status(thm)],[c_89,c_4])).

tff(c_30,plain,(
    ! [D_47,C_46,A_44,B_45] :
      ( r2_hidden(k1_funct_1(D_47,C_46),k2_relset_1(A_44,B_45,D_47))
      | k1_xboole_0 = B_45
      | ~ r2_hidden(C_46,A_44)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(D_47,A_44,B_45)
      | ~ v1_funct_1(D_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_746,plain,(
    ! [D_194,C_195,A_196,B_197] :
      ( r2_hidden(k1_funct_1(D_194,C_195),k2_relset_1(A_196,B_197,D_194))
      | B_197 = '#skF_2'
      | ~ r2_hidden(C_195,A_196)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_2(D_194,A_196,B_197)
      | ~ v1_funct_1(D_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_30])).

tff(c_751,plain,(
    ! [C_195] :
      ( r2_hidden(k1_funct_1('#skF_6',C_195),k2_relat_1('#skF_6'))
      | '#skF_5' = '#skF_2'
      | ~ r2_hidden(C_195,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_746])).

tff(c_757,plain,(
    ! [C_195] :
      ( r2_hidden(k1_funct_1('#skF_6',C_195),k2_relat_1('#skF_6'))
      | '#skF_5' = '#skF_2'
      | ~ r2_hidden(C_195,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_751])).

tff(c_760,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_757])).

tff(c_771,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_50])).

tff(c_774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_771])).

tff(c_778,plain,(
    ! [C_198] :
      ( r2_hidden(k1_funct_1('#skF_6',C_198),k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_198,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_757])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_787,plain,(
    ! [C_201,B_202] :
      ( r2_hidden(k1_funct_1('#skF_6',C_201),B_202)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_202)
      | ~ r2_hidden(C_201,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_778,c_2])).

tff(c_795,plain,(
    ! [C_203,B_204,B_205] :
      ( r2_hidden(k1_funct_1('#skF_6',C_203),B_204)
      | ~ r1_tarski(B_205,B_204)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_205)
      | ~ r2_hidden(C_203,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_787,c_2])).

tff(c_797,plain,(
    ! [C_203] :
      ( r2_hidden(k1_funct_1('#skF_6',C_203),k1_relat_1('#skF_7'))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_203,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_173,c_795])).

tff(c_825,plain,(
    ! [C_212] :
      ( r2_hidden(k1_funct_1('#skF_6',C_212),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_212,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_797])).

tff(c_26,plain,(
    ! [A_23,B_24,C_26] :
      ( k7_partfun1(A_23,B_24,C_26) = k1_funct_1(B_24,C_26)
      | ~ r2_hidden(C_26,k1_relat_1(B_24))
      | ~ v1_funct_1(B_24)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_827,plain,(
    ! [A_23,C_212] :
      ( k7_partfun1(A_23,'#skF_7',k1_funct_1('#skF_6',C_212)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_212))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_23)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_212,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_825,c_26])).

tff(c_866,plain,(
    ! [A_222,C_223] :
      ( k7_partfun1(A_222,'#skF_7',k1_funct_1('#skF_6',C_223)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_223))
      | ~ v5_relat_1('#skF_7',A_222)
      | ~ r2_hidden(C_223,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_42,c_827])).

tff(c_32,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_872,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_32])).

tff(c_878,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_872])).

tff(c_880,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_878])).

tff(c_883,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_880])).

tff(c_886,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_883])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    ! [A_6] :
      ( A_6 = '#skF_2'
      | ~ v1_xboole_0(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_8])).

tff(c_889,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_886,c_56])).

tff(c_893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_889])).

tff(c_894,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_878])).

tff(c_934,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_894])).

tff(c_938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:29:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.72  
% 3.80/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.80/1.72  
% 3.80/1.72  %Foreground sorts:
% 3.80/1.72  
% 3.80/1.72  
% 3.80/1.72  %Background operators:
% 3.80/1.72  
% 3.80/1.72  
% 3.80/1.72  %Foreground operators:
% 3.80/1.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.80/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.80/1.72  tff('#skF_7', type, '#skF_7': $i).
% 3.80/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.80/1.72  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.80/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.72  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.80/1.72  tff('#skF_6', type, '#skF_6': $i).
% 3.80/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.80/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.80/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.80/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.80/1.72  tff('#skF_8', type, '#skF_8': $i).
% 3.80/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.80/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.80/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.80/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.80/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.72  
% 3.80/1.74  tff(f_139, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.80/1.74  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.80/1.74  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.80/1.74  tff(f_38, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 3.80/1.74  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.80/1.74  tff(f_102, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.80/1.74  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.80/1.74  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.80/1.74  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.80/1.74  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.80/1.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.80/1.74  tff(f_114, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.80/1.74  tff(f_78, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.80/1.74  tff(c_38, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.80/1.74  tff(c_42, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.80/1.74  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.80/1.74  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.80/1.74  tff(c_151, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.80/1.74  tff(c_158, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_151])).
% 3.80/1.74  tff(c_138, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.80/1.74  tff(c_146, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_138])).
% 3.80/1.74  tff(c_36, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.80/1.74  tff(c_160, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_36])).
% 3.80/1.74  tff(c_173, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_160])).
% 3.80/1.74  tff(c_50, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.80/1.74  tff(c_10, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.80/1.74  tff(c_51, plain, (![A_59]: (k1_xboole_0=A_59 | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.80/1.74  tff(c_55, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_10, c_51])).
% 3.80/1.74  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.80/1.74  tff(c_57, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_34])).
% 3.80/1.74  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.80/1.74  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.80/1.74  tff(c_28, plain, (![C_29, B_28, D_37, E_41, A_27, F_43]: (k1_funct_1(k8_funct_2(B_28, C_29, A_27, D_37, E_41), F_43)=k1_funct_1(E_41, k1_funct_1(D_37, F_43)) | k1_xboole_0=B_28 | ~r1_tarski(k2_relset_1(B_28, C_29, D_37), k1_relset_1(C_29, A_27, E_41)) | ~m1_subset_1(F_43, B_28) | ~m1_subset_1(E_41, k1_zfmisc_1(k2_zfmisc_1(C_29, A_27))) | ~v1_funct_1(E_41) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(B_28, C_29))) | ~v1_funct_2(D_37, B_28, C_29) | ~v1_funct_1(D_37) | v1_xboole_0(C_29))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.80/1.74  tff(c_805, plain, (![B_210, C_207, F_209, E_208, A_211, D_206]: (k1_funct_1(k8_funct_2(B_210, C_207, A_211, D_206, E_208), F_209)=k1_funct_1(E_208, k1_funct_1(D_206, F_209)) | B_210='#skF_2' | ~r1_tarski(k2_relset_1(B_210, C_207, D_206), k1_relset_1(C_207, A_211, E_208)) | ~m1_subset_1(F_209, B_210) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(C_207, A_211))) | ~v1_funct_1(E_208) | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(B_210, C_207))) | ~v1_funct_2(D_206, B_210, C_207) | ~v1_funct_1(D_206) | v1_xboole_0(C_207))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_28])).
% 3.80/1.74  tff(c_807, plain, (![A_211, E_208, F_209]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_211, '#skF_6', E_208), F_209)=k1_funct_1(E_208, k1_funct_1('#skF_6', F_209)) | '#skF_2'='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_211, E_208)) | ~m1_subset_1(F_209, '#skF_4') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_211))) | ~v1_funct_1(E_208) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_805])).
% 3.80/1.74  tff(c_815, plain, (![A_211, E_208, F_209]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_211, '#skF_6', E_208), F_209)=k1_funct_1(E_208, k1_funct_1('#skF_6', F_209)) | '#skF_2'='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_211, E_208)) | ~m1_subset_1(F_209, '#skF_4') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_211))) | ~v1_funct_1(E_208) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_807])).
% 3.80/1.74  tff(c_849, plain, (![A_218, E_219, F_220]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_218, '#skF_6', E_219), F_220)=k1_funct_1(E_219, k1_funct_1('#skF_6', F_220)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_218, E_219)) | ~m1_subset_1(F_220, '#skF_4') | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_218))) | ~v1_funct_1(E_219))), inference(negUnitSimplification, [status(thm)], [c_50, c_57, c_815])).
% 3.80/1.74  tff(c_851, plain, (![F_220]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_220)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_220)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_220, '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_849])).
% 3.80/1.74  tff(c_853, plain, (![F_220]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_220)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_220)) | ~m1_subset_1(F_220, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_173, c_851])).
% 3.80/1.74  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.80/1.74  tff(c_96, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.80/1.74  tff(c_104, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_96])).
% 3.80/1.74  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.80/1.74  tff(c_69, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.80/1.74  tff(c_75, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_69])).
% 3.80/1.74  tff(c_81, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_75])).
% 3.80/1.74  tff(c_89, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), A_69) | r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.74  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.74  tff(c_94, plain, (![A_69]: (r1_tarski(A_69, A_69))), inference(resolution, [status(thm)], [c_89, c_4])).
% 3.80/1.74  tff(c_30, plain, (![D_47, C_46, A_44, B_45]: (r2_hidden(k1_funct_1(D_47, C_46), k2_relset_1(A_44, B_45, D_47)) | k1_xboole_0=B_45 | ~r2_hidden(C_46, A_44) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_2(D_47, A_44, B_45) | ~v1_funct_1(D_47))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.80/1.74  tff(c_746, plain, (![D_194, C_195, A_196, B_197]: (r2_hidden(k1_funct_1(D_194, C_195), k2_relset_1(A_196, B_197, D_194)) | B_197='#skF_2' | ~r2_hidden(C_195, A_196) | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_2(D_194, A_196, B_197) | ~v1_funct_1(D_194))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_30])).
% 3.80/1.74  tff(c_751, plain, (![C_195]: (r2_hidden(k1_funct_1('#skF_6', C_195), k2_relat_1('#skF_6')) | '#skF_5'='#skF_2' | ~r2_hidden(C_195, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_746])).
% 3.80/1.74  tff(c_757, plain, (![C_195]: (r2_hidden(k1_funct_1('#skF_6', C_195), k2_relat_1('#skF_6')) | '#skF_5'='#skF_2' | ~r2_hidden(C_195, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_751])).
% 3.80/1.74  tff(c_760, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_757])).
% 3.80/1.74  tff(c_771, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_50])).
% 3.80/1.74  tff(c_774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_771])).
% 3.80/1.74  tff(c_778, plain, (![C_198]: (r2_hidden(k1_funct_1('#skF_6', C_198), k2_relat_1('#skF_6')) | ~r2_hidden(C_198, '#skF_4'))), inference(splitRight, [status(thm)], [c_757])).
% 3.80/1.74  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.74  tff(c_787, plain, (![C_201, B_202]: (r2_hidden(k1_funct_1('#skF_6', C_201), B_202) | ~r1_tarski(k2_relat_1('#skF_6'), B_202) | ~r2_hidden(C_201, '#skF_4'))), inference(resolution, [status(thm)], [c_778, c_2])).
% 3.80/1.74  tff(c_795, plain, (![C_203, B_204, B_205]: (r2_hidden(k1_funct_1('#skF_6', C_203), B_204) | ~r1_tarski(B_205, B_204) | ~r1_tarski(k2_relat_1('#skF_6'), B_205) | ~r2_hidden(C_203, '#skF_4'))), inference(resolution, [status(thm)], [c_787, c_2])).
% 3.80/1.74  tff(c_797, plain, (![C_203]: (r2_hidden(k1_funct_1('#skF_6', C_203), k1_relat_1('#skF_7')) | ~r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~r2_hidden(C_203, '#skF_4'))), inference(resolution, [status(thm)], [c_173, c_795])).
% 3.80/1.74  tff(c_825, plain, (![C_212]: (r2_hidden(k1_funct_1('#skF_6', C_212), k1_relat_1('#skF_7')) | ~r2_hidden(C_212, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_797])).
% 3.80/1.74  tff(c_26, plain, (![A_23, B_24, C_26]: (k7_partfun1(A_23, B_24, C_26)=k1_funct_1(B_24, C_26) | ~r2_hidden(C_26, k1_relat_1(B_24)) | ~v1_funct_1(B_24) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.80/1.74  tff(c_827, plain, (![A_23, C_212]: (k7_partfun1(A_23, '#skF_7', k1_funct_1('#skF_6', C_212))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_212)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_23) | ~v1_relat_1('#skF_7') | ~r2_hidden(C_212, '#skF_4'))), inference(resolution, [status(thm)], [c_825, c_26])).
% 3.80/1.74  tff(c_866, plain, (![A_222, C_223]: (k7_partfun1(A_222, '#skF_7', k1_funct_1('#skF_6', C_223))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_223)) | ~v5_relat_1('#skF_7', A_222) | ~r2_hidden(C_223, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_42, c_827])).
% 3.80/1.74  tff(c_32, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.80/1.74  tff(c_872, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_866, c_32])).
% 3.80/1.74  tff(c_878, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_872])).
% 3.80/1.74  tff(c_880, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_878])).
% 3.80/1.74  tff(c_883, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_12, c_880])).
% 3.80/1.74  tff(c_886, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_883])).
% 3.80/1.74  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.80/1.74  tff(c_56, plain, (![A_6]: (A_6='#skF_2' | ~v1_xboole_0(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_8])).
% 3.80/1.74  tff(c_889, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_886, c_56])).
% 3.80/1.74  tff(c_893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_889])).
% 3.80/1.74  tff(c_894, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_878])).
% 3.80/1.74  tff(c_934, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_853, c_894])).
% 3.80/1.74  tff(c_938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_934])).
% 3.80/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.74  
% 3.80/1.74  Inference rules
% 3.80/1.74  ----------------------
% 3.80/1.74  #Ref     : 0
% 3.80/1.74  #Sup     : 187
% 3.80/1.74  #Fact    : 0
% 3.80/1.74  #Define  : 0
% 3.80/1.74  #Split   : 16
% 3.80/1.74  #Chain   : 0
% 3.80/1.74  #Close   : 0
% 3.80/1.74  
% 3.80/1.74  Ordering : KBO
% 3.80/1.74  
% 3.80/1.74  Simplification rules
% 3.80/1.74  ----------------------
% 3.80/1.74  #Subsume      : 36
% 3.80/1.74  #Demod        : 153
% 3.80/1.74  #Tautology    : 44
% 3.80/1.74  #SimpNegUnit  : 12
% 3.80/1.74  #BackRed      : 41
% 3.80/1.74  
% 3.80/1.74  #Partial instantiations: 0
% 3.80/1.74  #Strategies tried      : 1
% 3.80/1.74  
% 3.80/1.74  Timing (in seconds)
% 3.80/1.74  ----------------------
% 3.80/1.74  Preprocessing        : 0.38
% 3.80/1.74  Parsing              : 0.19
% 3.80/1.75  CNF conversion       : 0.03
% 3.80/1.75  Main loop            : 0.55
% 3.80/1.75  Inferencing          : 0.19
% 3.80/1.75  Reduction            : 0.18
% 3.80/1.75  Demodulation         : 0.12
% 3.80/1.75  BG Simplification    : 0.03
% 3.80/1.75  Subsumption          : 0.11
% 3.80/1.75  Abstraction          : 0.03
% 3.80/1.75  MUC search           : 0.00
% 3.80/1.75  Cooper               : 0.00
% 3.80/1.75  Total                : 0.97
% 3.80/1.75  Index Insertion      : 0.00
% 3.80/1.75  Index Deletion       : 0.00
% 3.80/1.75  Index Matching       : 0.00
% 3.80/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
