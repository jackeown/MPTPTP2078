%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:51 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 337 expanded)
%              Number of leaves         :   40 ( 135 expanded)
%              Depth                    :   15
%              Number of atoms          :  251 (1154 expanded)
%              Number of equality atoms :   57 ( 253 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

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

tff(f_130,negated_conjecture,(
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

tff(f_38,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_34,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_51,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_53,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_30])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_129,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_137,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_129])).

tff(c_32,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_142,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_32])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_24,plain,(
    ! [F_38,E_36,D_32,A_22,B_23,C_24] :
      ( k1_funct_1(k8_funct_2(B_23,C_24,A_22,D_32,E_36),F_38) = k1_funct_1(E_36,k1_funct_1(D_32,F_38))
      | k1_xboole_0 = B_23
      | ~ r1_tarski(k2_relset_1(B_23,C_24,D_32),k1_relset_1(C_24,A_22,E_36))
      | ~ m1_subset_1(F_38,B_23)
      | ~ m1_subset_1(E_36,k1_zfmisc_1(k2_zfmisc_1(C_24,A_22)))
      | ~ v1_funct_1(E_36)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(B_23,C_24)))
      | ~ v1_funct_2(D_32,B_23,C_24)
      | ~ v1_funct_1(D_32)
      | v1_xboole_0(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_687,plain,(
    ! [D_184,C_185,A_182,E_183,B_187,F_186] :
      ( k1_funct_1(k8_funct_2(B_187,C_185,A_182,D_184,E_183),F_186) = k1_funct_1(E_183,k1_funct_1(D_184,F_186))
      | B_187 = '#skF_2'
      | ~ r1_tarski(k2_relset_1(B_187,C_185,D_184),k1_relset_1(C_185,A_182,E_183))
      | ~ m1_subset_1(F_186,B_187)
      | ~ m1_subset_1(E_183,k1_zfmisc_1(k2_zfmisc_1(C_185,A_182)))
      | ~ v1_funct_1(E_183)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(B_187,C_185)))
      | ~ v1_funct_2(D_184,B_187,C_185)
      | ~ v1_funct_1(D_184)
      | v1_xboole_0(C_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_24])).

tff(c_689,plain,(
    ! [B_187,D_184,F_186] :
      ( k1_funct_1(k8_funct_2(B_187,'#skF_5','#skF_3',D_184,'#skF_7'),F_186) = k1_funct_1('#skF_7',k1_funct_1(D_184,F_186))
      | B_187 = '#skF_2'
      | ~ r1_tarski(k2_relset_1(B_187,'#skF_5',D_184),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_186,B_187)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(B_187,'#skF_5')))
      | ~ v1_funct_2(D_184,B_187,'#skF_5')
      | ~ v1_funct_1(D_184)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_687])).

tff(c_693,plain,(
    ! [B_187,D_184,F_186] :
      ( k1_funct_1(k8_funct_2(B_187,'#skF_5','#skF_3',D_184,'#skF_7'),F_186) = k1_funct_1('#skF_7',k1_funct_1(D_184,F_186))
      | B_187 = '#skF_2'
      | ~ r1_tarski(k2_relset_1(B_187,'#skF_5',D_184),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_186,B_187)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(B_187,'#skF_5')))
      | ~ v1_funct_2(D_184,B_187,'#skF_5')
      | ~ v1_funct_1(D_184)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_689])).

tff(c_1152,plain,(
    ! [B_254,D_255,F_256] :
      ( k1_funct_1(k8_funct_2(B_254,'#skF_5','#skF_3',D_255,'#skF_7'),F_256) = k1_funct_1('#skF_7',k1_funct_1(D_255,F_256))
      | B_254 = '#skF_2'
      | ~ r1_tarski(k2_relset_1(B_254,'#skF_5',D_255),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_256,B_254)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(B_254,'#skF_5')))
      | ~ v1_funct_2(D_255,B_254,'#skF_5')
      | ~ v1_funct_1(D_255) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_693])).

tff(c_1154,plain,(
    ! [F_256] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_256) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_256))
      | '#skF_2' = '#skF_4'
      | ~ m1_subset_1(F_256,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_142,c_1152])).

tff(c_1157,plain,(
    ! [F_256] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_256) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_256))
      | '#skF_2' = '#skF_4'
      | ~ m1_subset_1(F_256,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1154])).

tff(c_1158,plain,(
    ! [F_256] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_256) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_256))
      | ~ m1_subset_1(F_256,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1157])).

tff(c_64,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_87,plain,(
    ! [C_66,B_67,A_68] :
      ( v5_relat_1(C_66,B_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_94,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_147,plain,(
    ! [A_86,B_87,C_88] :
      ( k7_partfun1(A_86,B_87,C_88) = k1_funct_1(B_87,C_88)
      | ~ r2_hidden(C_88,k1_relat_1(B_87))
      | ~ v1_funct_1(B_87)
      | ~ v5_relat_1(B_87,A_86)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_702,plain,(
    ! [A_190,B_191,A_192] :
      ( k7_partfun1(A_190,B_191,A_192) = k1_funct_1(B_191,A_192)
      | ~ v1_funct_1(B_191)
      | ~ v5_relat_1(B_191,A_190)
      | ~ v1_relat_1(B_191)
      | v1_xboole_0(k1_relat_1(B_191))
      | ~ m1_subset_1(A_192,k1_relat_1(B_191)) ) ),
    inference(resolution,[status(thm)],[c_12,c_147])).

tff(c_706,plain,(
    ! [A_192] :
      ( k7_partfun1('#skF_5','#skF_6',A_192) = k1_funct_1('#skF_6',A_192)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_192,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_94,c_702])).

tff(c_712,plain,(
    ! [A_192] :
      ( k7_partfun1('#skF_5','#skF_6',A_192) = k1_funct_1('#skF_6',A_192)
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_192,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_44,c_706])).

tff(c_1087,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_712])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    ! [A_6] :
      ( A_6 = '#skF_2'
      | ~ v1_xboole_0(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_8])).

tff(c_1091,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1087,c_52])).

tff(c_136,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_129])).

tff(c_691,plain,(
    ! [B_187,D_184,F_186] :
      ( k1_funct_1(k8_funct_2(B_187,'#skF_4','#skF_5',D_184,'#skF_6'),F_186) = k1_funct_1('#skF_6',k1_funct_1(D_184,F_186))
      | B_187 = '#skF_2'
      | ~ r1_tarski(k2_relset_1(B_187,'#skF_4',D_184),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_186,B_187)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(B_187,'#skF_4')))
      | ~ v1_funct_2(D_184,B_187,'#skF_4')
      | ~ v1_funct_1(D_184)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_687])).

tff(c_696,plain,(
    ! [B_187,D_184,F_186] :
      ( k1_funct_1(k8_funct_2(B_187,'#skF_4','#skF_5',D_184,'#skF_6'),F_186) = k1_funct_1('#skF_6',k1_funct_1(D_184,F_186))
      | B_187 = '#skF_2'
      | ~ r1_tarski(k2_relset_1(B_187,'#skF_4',D_184),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_186,B_187)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(B_187,'#skF_4')))
      | ~ v1_funct_2(D_184,B_187,'#skF_4')
      | ~ v1_funct_1(D_184)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_691])).

tff(c_1241,plain,(
    ! [B_187,D_184,F_186] :
      ( k1_funct_1(k8_funct_2(B_187,'#skF_4','#skF_5',D_184,'#skF_6'),F_186) = k1_funct_1('#skF_6',k1_funct_1(D_184,F_186))
      | B_187 = '#skF_2'
      | ~ r1_tarski(k2_relset_1(B_187,'#skF_4',D_184),'#skF_2')
      | ~ m1_subset_1(F_186,B_187)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(B_187,'#skF_4')))
      | ~ v1_funct_2(D_184,B_187,'#skF_4')
      | ~ v1_funct_1(D_184)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1091,c_696])).

tff(c_1242,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1241])).

tff(c_1245,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1242,c_52])).

tff(c_1249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1245])).

tff(c_1251,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1241])).

tff(c_95,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_87])).

tff(c_72,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_64])).

tff(c_26,plain,(
    ! [D_42,C_41,A_39,B_40] :
      ( r2_hidden(k1_funct_1(D_42,C_41),k2_relset_1(A_39,B_40,D_42))
      | k1_xboole_0 = B_40
      | ~ r2_hidden(C_41,A_39)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_42,A_39,B_40)
      | ~ v1_funct_1(D_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_621,plain,(
    ! [D_165,C_166,A_167,B_168] :
      ( r2_hidden(k1_funct_1(D_165,C_166),k2_relset_1(A_167,B_168,D_165))
      | B_168 = '#skF_2'
      | ~ r2_hidden(C_166,A_167)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168)))
      | ~ v1_funct_2(D_165,A_167,B_168)
      | ~ v1_funct_1(D_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_26])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1252,plain,(
    ! [D_274,C_278,B_276,B_277,A_275] :
      ( r2_hidden(k1_funct_1(D_274,C_278),B_277)
      | ~ r1_tarski(k2_relset_1(A_275,B_276,D_274),B_277)
      | B_276 = '#skF_2'
      | ~ r2_hidden(C_278,A_275)
      | ~ m1_subset_1(D_274,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_funct_2(D_274,A_275,B_276)
      | ~ v1_funct_1(D_274) ) ),
    inference(resolution,[status(thm)],[c_621,c_2])).

tff(c_1254,plain,(
    ! [C_278] :
      ( r2_hidden(k1_funct_1('#skF_6',C_278),k1_relat_1('#skF_7'))
      | '#skF_5' = '#skF_2'
      | ~ r2_hidden(C_278,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_142,c_1252])).

tff(c_1260,plain,(
    ! [C_278] :
      ( r2_hidden(k1_funct_1('#skF_6',C_278),k1_relat_1('#skF_7'))
      | '#skF_5' = '#skF_2'
      | ~ r2_hidden(C_278,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1254])).

tff(c_1262,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1260])).

tff(c_1287,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_46])).

tff(c_1290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1287])).

tff(c_1293,plain,(
    ! [C_279] :
      ( r2_hidden(k1_funct_1('#skF_6',C_279),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_279,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1260])).

tff(c_22,plain,(
    ! [A_18,B_19,C_21] :
      ( k7_partfun1(A_18,B_19,C_21) = k1_funct_1(B_19,C_21)
      | ~ r2_hidden(C_21,k1_relat_1(B_19))
      | ~ v1_funct_1(B_19)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1295,plain,(
    ! [A_18,C_279] :
      ( k7_partfun1(A_18,'#skF_7',k1_funct_1('#skF_6',C_279)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_279))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_18)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_279,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1293,c_22])).

tff(c_1322,plain,(
    ! [A_285,C_286] :
      ( k7_partfun1(A_285,'#skF_7',k1_funct_1('#skF_6',C_286)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_286))
      | ~ v5_relat_1('#skF_7',A_285)
      | ~ r2_hidden(C_286,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_38,c_1295])).

tff(c_28,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1328,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_28])).

tff(c_1334,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1328])).

tff(c_1336,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1334])).

tff(c_1339,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1336])).

tff(c_1342,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1339])).

tff(c_1344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1251,c_1342])).

tff(c_1345,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1334])).

tff(c_1373,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_1345])).

tff(c_1377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.75  
% 3.77/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.77/1.75  
% 3.77/1.75  %Foreground sorts:
% 3.77/1.75  
% 3.77/1.75  
% 3.77/1.75  %Background operators:
% 3.77/1.75  
% 3.77/1.75  
% 3.77/1.75  %Foreground operators:
% 3.77/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.77/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.77/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.75  tff('#skF_7', type, '#skF_7': $i).
% 3.77/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.75  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.77/1.75  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.77/1.75  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.77/1.75  tff('#skF_6', type, '#skF_6': $i).
% 3.77/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.77/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.77/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.77/1.75  tff('#skF_8', type, '#skF_8': $i).
% 3.77/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.77/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.77/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.77/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.77/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.77/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.77/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.75  
% 3.77/1.77  tff(f_130, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.77/1.77  tff(f_38, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 3.77/1.77  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.77/1.77  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.77/1.77  tff(f_93, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.77/1.77  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.77/1.77  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.77/1.77  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.77/1.77  tff(f_69, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.77/1.77  tff(f_105, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.77/1.77  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.77/1.77  tff(c_34, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.77/1.77  tff(c_10, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.77/1.77  tff(c_47, plain, (![A_54]: (k1_xboole_0=A_54 | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.77/1.77  tff(c_51, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_10, c_47])).
% 3.77/1.77  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.77/1.77  tff(c_53, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_30])).
% 3.77/1.77  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.77/1.77  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.77/1.77  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.77/1.77  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.77/1.77  tff(c_129, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.77/1.77  tff(c_137, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_129])).
% 3.77/1.77  tff(c_32, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.77/1.77  tff(c_142, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_32])).
% 3.77/1.77  tff(c_46, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.77/1.77  tff(c_38, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.77/1.77  tff(c_24, plain, (![F_38, E_36, D_32, A_22, B_23, C_24]: (k1_funct_1(k8_funct_2(B_23, C_24, A_22, D_32, E_36), F_38)=k1_funct_1(E_36, k1_funct_1(D_32, F_38)) | k1_xboole_0=B_23 | ~r1_tarski(k2_relset_1(B_23, C_24, D_32), k1_relset_1(C_24, A_22, E_36)) | ~m1_subset_1(F_38, B_23) | ~m1_subset_1(E_36, k1_zfmisc_1(k2_zfmisc_1(C_24, A_22))) | ~v1_funct_1(E_36) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1(B_23, C_24))) | ~v1_funct_2(D_32, B_23, C_24) | ~v1_funct_1(D_32) | v1_xboole_0(C_24))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.77/1.77  tff(c_687, plain, (![D_184, C_185, A_182, E_183, B_187, F_186]: (k1_funct_1(k8_funct_2(B_187, C_185, A_182, D_184, E_183), F_186)=k1_funct_1(E_183, k1_funct_1(D_184, F_186)) | B_187='#skF_2' | ~r1_tarski(k2_relset_1(B_187, C_185, D_184), k1_relset_1(C_185, A_182, E_183)) | ~m1_subset_1(F_186, B_187) | ~m1_subset_1(E_183, k1_zfmisc_1(k2_zfmisc_1(C_185, A_182))) | ~v1_funct_1(E_183) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(B_187, C_185))) | ~v1_funct_2(D_184, B_187, C_185) | ~v1_funct_1(D_184) | v1_xboole_0(C_185))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_24])).
% 3.77/1.77  tff(c_689, plain, (![B_187, D_184, F_186]: (k1_funct_1(k8_funct_2(B_187, '#skF_5', '#skF_3', D_184, '#skF_7'), F_186)=k1_funct_1('#skF_7', k1_funct_1(D_184, F_186)) | B_187='#skF_2' | ~r1_tarski(k2_relset_1(B_187, '#skF_5', D_184), k1_relat_1('#skF_7')) | ~m1_subset_1(F_186, B_187) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(B_187, '#skF_5'))) | ~v1_funct_2(D_184, B_187, '#skF_5') | ~v1_funct_1(D_184) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_687])).
% 3.77/1.77  tff(c_693, plain, (![B_187, D_184, F_186]: (k1_funct_1(k8_funct_2(B_187, '#skF_5', '#skF_3', D_184, '#skF_7'), F_186)=k1_funct_1('#skF_7', k1_funct_1(D_184, F_186)) | B_187='#skF_2' | ~r1_tarski(k2_relset_1(B_187, '#skF_5', D_184), k1_relat_1('#skF_7')) | ~m1_subset_1(F_186, B_187) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(B_187, '#skF_5'))) | ~v1_funct_2(D_184, B_187, '#skF_5') | ~v1_funct_1(D_184) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_689])).
% 3.77/1.77  tff(c_1152, plain, (![B_254, D_255, F_256]: (k1_funct_1(k8_funct_2(B_254, '#skF_5', '#skF_3', D_255, '#skF_7'), F_256)=k1_funct_1('#skF_7', k1_funct_1(D_255, F_256)) | B_254='#skF_2' | ~r1_tarski(k2_relset_1(B_254, '#skF_5', D_255), k1_relat_1('#skF_7')) | ~m1_subset_1(F_256, B_254) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(B_254, '#skF_5'))) | ~v1_funct_2(D_255, B_254, '#skF_5') | ~v1_funct_1(D_255))), inference(negUnitSimplification, [status(thm)], [c_46, c_693])).
% 3.77/1.77  tff(c_1154, plain, (![F_256]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_256)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_256)) | '#skF_2'='#skF_4' | ~m1_subset_1(F_256, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_142, c_1152])).
% 3.77/1.77  tff(c_1157, plain, (![F_256]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_256)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_256)) | '#skF_2'='#skF_4' | ~m1_subset_1(F_256, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1154])).
% 3.77/1.77  tff(c_1158, plain, (![F_256]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_256)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_256)) | ~m1_subset_1(F_256, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_53, c_1157])).
% 3.77/1.77  tff(c_64, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.77/1.77  tff(c_71, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_64])).
% 3.77/1.77  tff(c_87, plain, (![C_66, B_67, A_68]: (v5_relat_1(C_66, B_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.77/1.77  tff(c_94, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_87])).
% 3.77/1.77  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.77/1.77  tff(c_147, plain, (![A_86, B_87, C_88]: (k7_partfun1(A_86, B_87, C_88)=k1_funct_1(B_87, C_88) | ~r2_hidden(C_88, k1_relat_1(B_87)) | ~v1_funct_1(B_87) | ~v5_relat_1(B_87, A_86) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.77/1.77  tff(c_702, plain, (![A_190, B_191, A_192]: (k7_partfun1(A_190, B_191, A_192)=k1_funct_1(B_191, A_192) | ~v1_funct_1(B_191) | ~v5_relat_1(B_191, A_190) | ~v1_relat_1(B_191) | v1_xboole_0(k1_relat_1(B_191)) | ~m1_subset_1(A_192, k1_relat_1(B_191)))), inference(resolution, [status(thm)], [c_12, c_147])).
% 3.77/1.77  tff(c_706, plain, (![A_192]: (k7_partfun1('#skF_5', '#skF_6', A_192)=k1_funct_1('#skF_6', A_192) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_192, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_94, c_702])).
% 3.77/1.77  tff(c_712, plain, (![A_192]: (k7_partfun1('#skF_5', '#skF_6', A_192)=k1_funct_1('#skF_6', A_192) | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_192, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_44, c_706])).
% 3.77/1.77  tff(c_1087, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_712])).
% 3.77/1.77  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.77/1.77  tff(c_52, plain, (![A_6]: (A_6='#skF_2' | ~v1_xboole_0(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_8])).
% 3.77/1.77  tff(c_1091, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(resolution, [status(thm)], [c_1087, c_52])).
% 3.77/1.77  tff(c_136, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_129])).
% 3.77/1.77  tff(c_691, plain, (![B_187, D_184, F_186]: (k1_funct_1(k8_funct_2(B_187, '#skF_4', '#skF_5', D_184, '#skF_6'), F_186)=k1_funct_1('#skF_6', k1_funct_1(D_184, F_186)) | B_187='#skF_2' | ~r1_tarski(k2_relset_1(B_187, '#skF_4', D_184), k1_relat_1('#skF_6')) | ~m1_subset_1(F_186, B_187) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(B_187, '#skF_4'))) | ~v1_funct_2(D_184, B_187, '#skF_4') | ~v1_funct_1(D_184) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_687])).
% 3.77/1.77  tff(c_696, plain, (![B_187, D_184, F_186]: (k1_funct_1(k8_funct_2(B_187, '#skF_4', '#skF_5', D_184, '#skF_6'), F_186)=k1_funct_1('#skF_6', k1_funct_1(D_184, F_186)) | B_187='#skF_2' | ~r1_tarski(k2_relset_1(B_187, '#skF_4', D_184), k1_relat_1('#skF_6')) | ~m1_subset_1(F_186, B_187) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(B_187, '#skF_4'))) | ~v1_funct_2(D_184, B_187, '#skF_4') | ~v1_funct_1(D_184) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_691])).
% 3.77/1.77  tff(c_1241, plain, (![B_187, D_184, F_186]: (k1_funct_1(k8_funct_2(B_187, '#skF_4', '#skF_5', D_184, '#skF_6'), F_186)=k1_funct_1('#skF_6', k1_funct_1(D_184, F_186)) | B_187='#skF_2' | ~r1_tarski(k2_relset_1(B_187, '#skF_4', D_184), '#skF_2') | ~m1_subset_1(F_186, B_187) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(B_187, '#skF_4'))) | ~v1_funct_2(D_184, B_187, '#skF_4') | ~v1_funct_1(D_184) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1091, c_696])).
% 3.77/1.77  tff(c_1242, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1241])).
% 3.77/1.77  tff(c_1245, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_1242, c_52])).
% 3.77/1.77  tff(c_1249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1245])).
% 3.77/1.77  tff(c_1251, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1241])).
% 3.77/1.77  tff(c_95, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_87])).
% 3.77/1.77  tff(c_72, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_64])).
% 3.77/1.77  tff(c_26, plain, (![D_42, C_41, A_39, B_40]: (r2_hidden(k1_funct_1(D_42, C_41), k2_relset_1(A_39, B_40, D_42)) | k1_xboole_0=B_40 | ~r2_hidden(C_41, A_39) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_42, A_39, B_40) | ~v1_funct_1(D_42))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.77/1.77  tff(c_621, plain, (![D_165, C_166, A_167, B_168]: (r2_hidden(k1_funct_1(D_165, C_166), k2_relset_1(A_167, B_168, D_165)) | B_168='#skF_2' | ~r2_hidden(C_166, A_167) | ~m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))) | ~v1_funct_2(D_165, A_167, B_168) | ~v1_funct_1(D_165))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_26])).
% 3.77/1.77  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/1.77  tff(c_1252, plain, (![D_274, C_278, B_276, B_277, A_275]: (r2_hidden(k1_funct_1(D_274, C_278), B_277) | ~r1_tarski(k2_relset_1(A_275, B_276, D_274), B_277) | B_276='#skF_2' | ~r2_hidden(C_278, A_275) | ~m1_subset_1(D_274, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_funct_2(D_274, A_275, B_276) | ~v1_funct_1(D_274))), inference(resolution, [status(thm)], [c_621, c_2])).
% 3.77/1.77  tff(c_1254, plain, (![C_278]: (r2_hidden(k1_funct_1('#skF_6', C_278), k1_relat_1('#skF_7')) | '#skF_5'='#skF_2' | ~r2_hidden(C_278, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_142, c_1252])).
% 3.77/1.77  tff(c_1260, plain, (![C_278]: (r2_hidden(k1_funct_1('#skF_6', C_278), k1_relat_1('#skF_7')) | '#skF_5'='#skF_2' | ~r2_hidden(C_278, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1254])).
% 3.77/1.77  tff(c_1262, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_1260])).
% 3.77/1.77  tff(c_1287, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1262, c_46])).
% 3.77/1.77  tff(c_1290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1287])).
% 3.77/1.77  tff(c_1293, plain, (![C_279]: (r2_hidden(k1_funct_1('#skF_6', C_279), k1_relat_1('#skF_7')) | ~r2_hidden(C_279, '#skF_4'))), inference(splitRight, [status(thm)], [c_1260])).
% 3.77/1.77  tff(c_22, plain, (![A_18, B_19, C_21]: (k7_partfun1(A_18, B_19, C_21)=k1_funct_1(B_19, C_21) | ~r2_hidden(C_21, k1_relat_1(B_19)) | ~v1_funct_1(B_19) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.77/1.77  tff(c_1295, plain, (![A_18, C_279]: (k7_partfun1(A_18, '#skF_7', k1_funct_1('#skF_6', C_279))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_279)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_18) | ~v1_relat_1('#skF_7') | ~r2_hidden(C_279, '#skF_4'))), inference(resolution, [status(thm)], [c_1293, c_22])).
% 3.77/1.77  tff(c_1322, plain, (![A_285, C_286]: (k7_partfun1(A_285, '#skF_7', k1_funct_1('#skF_6', C_286))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_286)) | ~v5_relat_1('#skF_7', A_285) | ~r2_hidden(C_286, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_38, c_1295])).
% 3.77/1.77  tff(c_28, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.77/1.77  tff(c_1328, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1322, c_28])).
% 3.77/1.77  tff(c_1334, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_1328])).
% 3.77/1.77  tff(c_1336, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_1334])).
% 3.77/1.77  tff(c_1339, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_12, c_1336])).
% 3.77/1.77  tff(c_1342, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1339])).
% 3.77/1.77  tff(c_1344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1251, c_1342])).
% 3.77/1.77  tff(c_1345, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_1334])).
% 3.77/1.77  tff(c_1373, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1158, c_1345])).
% 3.77/1.77  tff(c_1377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1373])).
% 3.77/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.77  
% 3.77/1.77  Inference rules
% 3.77/1.77  ----------------------
% 3.77/1.77  #Ref     : 0
% 3.77/1.77  #Sup     : 269
% 3.77/1.77  #Fact    : 0
% 3.77/1.77  #Define  : 0
% 3.77/1.77  #Split   : 26
% 3.77/1.77  #Chain   : 0
% 3.77/1.77  #Close   : 0
% 3.77/1.77  
% 3.77/1.77  Ordering : KBO
% 3.77/1.77  
% 3.77/1.77  Simplification rules
% 3.77/1.77  ----------------------
% 3.77/1.77  #Subsume      : 53
% 3.77/1.77  #Demod        : 262
% 3.77/1.77  #Tautology    : 79
% 3.77/1.77  #SimpNegUnit  : 16
% 3.77/1.77  #BackRed      : 89
% 3.77/1.77  
% 3.77/1.77  #Partial instantiations: 0
% 3.77/1.77  #Strategies tried      : 1
% 3.77/1.77  
% 3.77/1.77  Timing (in seconds)
% 3.77/1.77  ----------------------
% 3.77/1.77  Preprocessing        : 0.35
% 3.77/1.77  Parsing              : 0.19
% 3.77/1.77  CNF conversion       : 0.03
% 3.77/1.77  Main loop            : 0.56
% 3.77/1.78  Inferencing          : 0.20
% 3.77/1.78  Reduction            : 0.18
% 3.77/1.78  Demodulation         : 0.12
% 3.77/1.78  BG Simplification    : 0.03
% 3.77/1.78  Subsumption          : 0.11
% 3.77/1.78  Abstraction          : 0.03
% 3.77/1.78  MUC search           : 0.00
% 3.77/1.78  Cooper               : 0.00
% 3.77/1.78  Total                : 0.94
% 3.77/1.78  Index Insertion      : 0.00
% 3.77/1.78  Index Deletion       : 0.00
% 3.77/1.78  Index Matching       : 0.00
% 3.77/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
