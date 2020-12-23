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
% DateTime   : Thu Dec  3 10:17:50 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 315 expanded)
%              Number of leaves         :   44 ( 128 expanded)
%              Depth                    :   14
%              Number of atoms          :  228 (1087 expanded)
%              Number of equality atoms :   52 ( 261 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_173,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_relset_1(A_93,B_94,C_95) = k2_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_180,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_173])).

tff(c_151,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_159,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_151])).

tff(c_50,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_164,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_50])).

tff(c_182,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_164])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_361,plain,(
    ! [B_133,E_132,D_130,F_129,A_131,C_134] :
      ( k1_funct_1(k8_funct_2(B_133,C_134,A_131,D_130,E_132),F_129) = k1_funct_1(E_132,k1_funct_1(D_130,F_129))
      | k1_xboole_0 = B_133
      | ~ r1_tarski(k2_relset_1(B_133,C_134,D_130),k1_relset_1(C_134,A_131,E_132))
      | ~ m1_subset_1(F_129,B_133)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(C_134,A_131)))
      | ~ v1_funct_1(E_132)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(k2_zfmisc_1(B_133,C_134)))
      | ~ v1_funct_2(D_130,B_133,C_134)
      | ~ v1_funct_1(D_130)
      | v1_xboole_0(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_367,plain,(
    ! [A_131,E_132,F_129] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_131,'#skF_5',E_132),F_129) = k1_funct_1(E_132,k1_funct_1('#skF_5',F_129))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_131,E_132))
      | ~ m1_subset_1(F_129,'#skF_3')
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_131)))
      | ~ v1_funct_1(E_132)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_361])).

tff(c_377,plain,(
    ! [A_131,E_132,F_129] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_131,'#skF_5',E_132),F_129) = k1_funct_1(E_132,k1_funct_1('#skF_5',F_129))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_131,E_132))
      | ~ m1_subset_1(F_129,'#skF_3')
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_131)))
      | ~ v1_funct_1(E_132)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_367])).

tff(c_418,plain,(
    ! [A_139,E_140,F_141] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_139,'#skF_5',E_140),F_141) = k1_funct_1(E_140,k1_funct_1('#skF_5',F_141))
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_139,E_140))
      | ~ m1_subset_1(F_141,'#skF_3')
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48,c_377])).

tff(c_420,plain,(
    ! [F_141] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_141) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_141))
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_141,'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_418])).

tff(c_425,plain,(
    ! [F_141] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_141) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_141))
      | ~ m1_subset_1(F_141,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_182,c_420])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_96,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_89])).

tff(c_158,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_151])).

tff(c_261,plain,(
    ! [B_116,A_117,C_118] :
      ( k1_xboole_0 = B_116
      | k1_relset_1(A_117,B_116,C_118) = A_117
      | ~ v1_funct_2(C_118,A_117,B_116)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_264,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_261])).

tff(c_270,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_158,c_264])).

tff(c_274,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_289,plain,(
    ! [A_119,B_120,C_121] :
      ( k7_partfun1(A_119,B_120,C_121) = k1_funct_1(B_120,C_121)
      | ~ r2_hidden(C_121,k1_relat_1(B_120))
      | ~ v1_funct_1(B_120)
      | ~ v5_relat_1(B_120,A_119)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_291,plain,(
    ! [A_119,C_121] :
      ( k7_partfun1(A_119,'#skF_5',C_121) = k1_funct_1('#skF_5',C_121)
      | ~ r2_hidden(C_121,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_119)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_289])).

tff(c_316,plain,(
    ! [A_123,C_124] :
      ( k7_partfun1(A_123,'#skF_5',C_124) = k1_funct_1('#skF_5',C_124)
      | ~ r2_hidden(C_124,'#skF_3')
      | ~ v5_relat_1('#skF_5',A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_62,c_291])).

tff(c_328,plain,(
    ! [A_123] :
      ( k7_partfun1(A_123,'#skF_5','#skF_1'('#skF_3')) = k1_funct_1('#skF_5','#skF_1'('#skF_3'))
      | ~ v5_relat_1('#skF_5',A_123)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4,c_316])).

tff(c_329,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_332,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_329,c_6])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_332])).

tff(c_338,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_141,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_149,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_141])).

tff(c_97,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_89])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( v5_relat_1(B_10,A_9)
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_189,plain,
    ( v5_relat_1('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_182,c_12])).

tff(c_195,plain,(
    v5_relat_1('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_189])).

tff(c_16,plain,(
    ! [B_12,C_14,A_11] :
      ( r2_hidden(k1_funct_1(B_12,C_14),A_11)
      | ~ r2_hidden(C_14,k1_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_622,plain,(
    ! [A_175,B_176,B_177,C_178] :
      ( k7_partfun1(A_175,B_176,k1_funct_1(B_177,C_178)) = k1_funct_1(B_176,k1_funct_1(B_177,C_178))
      | ~ v1_funct_1(B_176)
      | ~ v5_relat_1(B_176,A_175)
      | ~ v1_relat_1(B_176)
      | ~ r2_hidden(C_178,k1_relat_1(B_177))
      | ~ v1_funct_1(B_177)
      | ~ v5_relat_1(B_177,k1_relat_1(B_176))
      | ~ v1_relat_1(B_177) ) ),
    inference(resolution,[status(thm)],[c_16,c_289])).

tff(c_624,plain,(
    ! [A_175,B_176,C_178] :
      ( k7_partfun1(A_175,B_176,k1_funct_1('#skF_5',C_178)) = k1_funct_1(B_176,k1_funct_1('#skF_5',C_178))
      | ~ v1_funct_1(B_176)
      | ~ v5_relat_1(B_176,A_175)
      | ~ v1_relat_1(B_176)
      | ~ r2_hidden(C_178,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k1_relat_1(B_176))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_622])).

tff(c_639,plain,(
    ! [A_179,B_180,C_181] :
      ( k7_partfun1(A_179,B_180,k1_funct_1('#skF_5',C_181)) = k1_funct_1(B_180,k1_funct_1('#skF_5',C_181))
      | ~ v1_funct_1(B_180)
      | ~ v5_relat_1(B_180,A_179)
      | ~ v1_relat_1(B_180)
      | ~ r2_hidden(C_181,'#skF_3')
      | ~ v5_relat_1('#skF_5',k1_relat_1(B_180)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_62,c_624])).

tff(c_643,plain,(
    ! [A_179,C_181] :
      ( k7_partfun1(A_179,'#skF_6',k1_funct_1('#skF_5',C_181)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_181))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_179)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_181,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_195,c_639])).

tff(c_649,plain,(
    ! [A_182,C_183] :
      ( k7_partfun1(A_182,'#skF_6',k1_funct_1('#skF_5',C_183)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_183))
      | ~ v5_relat_1('#skF_6',A_182)
      | ~ r2_hidden(C_183,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_56,c_643])).

tff(c_46,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_655,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_46])).

tff(c_661,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_655])).

tff(c_663,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_661])).

tff(c_666,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_663])).

tff(c_669,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_666])).

tff(c_671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_669])).

tff(c_672,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_661])).

tff(c_713,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_672])).

tff(c_717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_713])).

tff(c_718,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_70] :
      ( v1_xboole_0(A_70)
      | r2_hidden('#skF_1'(A_70),A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_78,plain,(
    ! [A_71] :
      ( ~ r1_tarski(A_71,'#skF_1'(A_71))
      | v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_69,c_18])).

tff(c_83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_739,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_83])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/2.03  
% 4.15/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/2.03  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.15/2.03  
% 4.15/2.03  %Foreground sorts:
% 4.15/2.03  
% 4.15/2.03  
% 4.15/2.03  %Background operators:
% 4.15/2.03  
% 4.15/2.03  
% 4.15/2.03  %Foreground operators:
% 4.15/2.03  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.15/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.15/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.15/2.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.15/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.15/2.03  tff('#skF_7', type, '#skF_7': $i).
% 4.15/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.15/2.03  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.15/2.03  tff('#skF_5', type, '#skF_5': $i).
% 4.15/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.15/2.03  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.15/2.03  tff('#skF_6', type, '#skF_6': $i).
% 4.15/2.03  tff('#skF_2', type, '#skF_2': $i).
% 4.15/2.03  tff('#skF_3', type, '#skF_3': $i).
% 4.15/2.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.15/2.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.15/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.15/2.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.15/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.15/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.15/2.03  tff('#skF_4', type, '#skF_4': $i).
% 4.15/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/2.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.15/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.15/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.15/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/2.03  
% 4.15/2.05  tff(f_161, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 4.15/2.05  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.15/2.05  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.15/2.05  tff(f_136, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 4.15/2.05  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.15/2.05  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.15/2.05  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.15/2.05  tff(f_112, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 4.15/2.05  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.15/2.05  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.15/2.05  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.15/2.05  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.15/2.05  tff(f_60, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 4.15/2.05  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.15/2.05  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.15/2.05  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/2.05  tff(c_52, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/2.05  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/2.05  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/2.05  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/2.05  tff(c_173, plain, (![A_93, B_94, C_95]: (k2_relset_1(A_93, B_94, C_95)=k2_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.15/2.05  tff(c_180, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_173])).
% 4.15/2.05  tff(c_151, plain, (![A_90, B_91, C_92]: (k1_relset_1(A_90, B_91, C_92)=k1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.15/2.05  tff(c_159, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_151])).
% 4.15/2.05  tff(c_50, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/2.05  tff(c_164, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_50])).
% 4.15/2.05  tff(c_182, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_164])).
% 4.15/2.05  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/2.05  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/2.05  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/2.05  tff(c_361, plain, (![B_133, E_132, D_130, F_129, A_131, C_134]: (k1_funct_1(k8_funct_2(B_133, C_134, A_131, D_130, E_132), F_129)=k1_funct_1(E_132, k1_funct_1(D_130, F_129)) | k1_xboole_0=B_133 | ~r1_tarski(k2_relset_1(B_133, C_134, D_130), k1_relset_1(C_134, A_131, E_132)) | ~m1_subset_1(F_129, B_133) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(C_134, A_131))) | ~v1_funct_1(E_132) | ~m1_subset_1(D_130, k1_zfmisc_1(k2_zfmisc_1(B_133, C_134))) | ~v1_funct_2(D_130, B_133, C_134) | ~v1_funct_1(D_130) | v1_xboole_0(C_134))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.15/2.05  tff(c_367, plain, (![A_131, E_132, F_129]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_131, '#skF_5', E_132), F_129)=k1_funct_1(E_132, k1_funct_1('#skF_5', F_129)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_131, E_132)) | ~m1_subset_1(F_129, '#skF_3') | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_131))) | ~v1_funct_1(E_132) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_180, c_361])).
% 4.15/2.05  tff(c_377, plain, (![A_131, E_132, F_129]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_131, '#skF_5', E_132), F_129)=k1_funct_1(E_132, k1_funct_1('#skF_5', F_129)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_131, E_132)) | ~m1_subset_1(F_129, '#skF_3') | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_131))) | ~v1_funct_1(E_132) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_367])).
% 4.15/2.05  tff(c_418, plain, (![A_139, E_140, F_141]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_139, '#skF_5', E_140), F_141)=k1_funct_1(E_140, k1_funct_1('#skF_5', F_141)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_139, E_140)) | ~m1_subset_1(F_141, '#skF_3') | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_139))) | ~v1_funct_1(E_140))), inference(negUnitSimplification, [status(thm)], [c_64, c_48, c_377])).
% 4.15/2.05  tff(c_420, plain, (![F_141]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_141)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_141)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~m1_subset_1(F_141, '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_418])).
% 4.15/2.05  tff(c_425, plain, (![F_141]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_141)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_141)) | ~m1_subset_1(F_141, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_182, c_420])).
% 4.15/2.05  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.15/2.05  tff(c_89, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.15/2.05  tff(c_96, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_89])).
% 4.15/2.05  tff(c_158, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_151])).
% 4.15/2.05  tff(c_261, plain, (![B_116, A_117, C_118]: (k1_xboole_0=B_116 | k1_relset_1(A_117, B_116, C_118)=A_117 | ~v1_funct_2(C_118, A_117, B_116) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.15/2.05  tff(c_264, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_261])).
% 4.15/2.05  tff(c_270, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_158, c_264])).
% 4.15/2.05  tff(c_274, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_270])).
% 4.15/2.05  tff(c_289, plain, (![A_119, B_120, C_121]: (k7_partfun1(A_119, B_120, C_121)=k1_funct_1(B_120, C_121) | ~r2_hidden(C_121, k1_relat_1(B_120)) | ~v1_funct_1(B_120) | ~v5_relat_1(B_120, A_119) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.15/2.05  tff(c_291, plain, (![A_119, C_121]: (k7_partfun1(A_119, '#skF_5', C_121)=k1_funct_1('#skF_5', C_121) | ~r2_hidden(C_121, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_119) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_289])).
% 4.15/2.05  tff(c_316, plain, (![A_123, C_124]: (k7_partfun1(A_123, '#skF_5', C_124)=k1_funct_1('#skF_5', C_124) | ~r2_hidden(C_124, '#skF_3') | ~v5_relat_1('#skF_5', A_123))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_62, c_291])).
% 4.15/2.05  tff(c_328, plain, (![A_123]: (k7_partfun1(A_123, '#skF_5', '#skF_1'('#skF_3'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3')) | ~v5_relat_1('#skF_5', A_123) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_316])).
% 4.15/2.05  tff(c_329, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_328])).
% 4.15/2.05  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.15/2.05  tff(c_332, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_329, c_6])).
% 4.15/2.05  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_332])).
% 4.15/2.05  tff(c_338, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_328])).
% 4.15/2.05  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.15/2.05  tff(c_141, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.15/2.05  tff(c_149, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_141])).
% 4.15/2.05  tff(c_97, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_89])).
% 4.15/2.05  tff(c_12, plain, (![B_10, A_9]: (v5_relat_1(B_10, A_9) | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.15/2.05  tff(c_189, plain, (v5_relat_1('#skF_5', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_182, c_12])).
% 4.15/2.05  tff(c_195, plain, (v5_relat_1('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_189])).
% 4.15/2.05  tff(c_16, plain, (![B_12, C_14, A_11]: (r2_hidden(k1_funct_1(B_12, C_14), A_11) | ~r2_hidden(C_14, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/2.05  tff(c_622, plain, (![A_175, B_176, B_177, C_178]: (k7_partfun1(A_175, B_176, k1_funct_1(B_177, C_178))=k1_funct_1(B_176, k1_funct_1(B_177, C_178)) | ~v1_funct_1(B_176) | ~v5_relat_1(B_176, A_175) | ~v1_relat_1(B_176) | ~r2_hidden(C_178, k1_relat_1(B_177)) | ~v1_funct_1(B_177) | ~v5_relat_1(B_177, k1_relat_1(B_176)) | ~v1_relat_1(B_177))), inference(resolution, [status(thm)], [c_16, c_289])).
% 4.15/2.05  tff(c_624, plain, (![A_175, B_176, C_178]: (k7_partfun1(A_175, B_176, k1_funct_1('#skF_5', C_178))=k1_funct_1(B_176, k1_funct_1('#skF_5', C_178)) | ~v1_funct_1(B_176) | ~v5_relat_1(B_176, A_175) | ~v1_relat_1(B_176) | ~r2_hidden(C_178, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', k1_relat_1(B_176)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_622])).
% 4.15/2.05  tff(c_639, plain, (![A_179, B_180, C_181]: (k7_partfun1(A_179, B_180, k1_funct_1('#skF_5', C_181))=k1_funct_1(B_180, k1_funct_1('#skF_5', C_181)) | ~v1_funct_1(B_180) | ~v5_relat_1(B_180, A_179) | ~v1_relat_1(B_180) | ~r2_hidden(C_181, '#skF_3') | ~v5_relat_1('#skF_5', k1_relat_1(B_180)))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_62, c_624])).
% 4.15/2.05  tff(c_643, plain, (![A_179, C_181]: (k7_partfun1(A_179, '#skF_6', k1_funct_1('#skF_5', C_181))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_181)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_179) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_181, '#skF_3'))), inference(resolution, [status(thm)], [c_195, c_639])).
% 4.15/2.05  tff(c_649, plain, (![A_182, C_183]: (k7_partfun1(A_182, '#skF_6', k1_funct_1('#skF_5', C_183))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_183)) | ~v5_relat_1('#skF_6', A_182) | ~r2_hidden(C_183, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_56, c_643])).
% 4.15/2.05  tff(c_46, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.15/2.05  tff(c_655, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_649, c_46])).
% 4.15/2.05  tff(c_661, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_655])).
% 4.15/2.05  tff(c_663, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_661])).
% 4.15/2.05  tff(c_666, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_663])).
% 4.15/2.05  tff(c_669, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_666])).
% 4.15/2.05  tff(c_671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_338, c_669])).
% 4.15/2.05  tff(c_672, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_661])).
% 4.15/2.05  tff(c_713, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_425, c_672])).
% 4.15/2.05  tff(c_717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_713])).
% 4.15/2.05  tff(c_718, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_270])).
% 4.15/2.05  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.15/2.05  tff(c_69, plain, (![A_70]: (v1_xboole_0(A_70) | r2_hidden('#skF_1'(A_70), A_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.15/2.05  tff(c_18, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.15/2.05  tff(c_78, plain, (![A_71]: (~r1_tarski(A_71, '#skF_1'(A_71)) | v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_69, c_18])).
% 4.15/2.05  tff(c_83, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_78])).
% 4.15/2.05  tff(c_739, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_83])).
% 4.15/2.05  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_739])).
% 4.15/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/2.05  
% 4.15/2.05  Inference rules
% 4.15/2.05  ----------------------
% 4.15/2.05  #Ref     : 0
% 4.15/2.05  #Sup     : 137
% 4.15/2.05  #Fact    : 0
% 4.15/2.05  #Define  : 0
% 4.15/2.05  #Split   : 12
% 4.15/2.05  #Chain   : 0
% 4.15/2.05  #Close   : 0
% 4.15/2.05  
% 4.15/2.05  Ordering : KBO
% 4.15/2.05  
% 4.15/2.05  Simplification rules
% 4.15/2.05  ----------------------
% 4.15/2.05  #Subsume      : 24
% 4.15/2.05  #Demod        : 140
% 4.15/2.05  #Tautology    : 39
% 4.15/2.05  #SimpNegUnit  : 18
% 4.15/2.05  #BackRed      : 13
% 4.15/2.05  
% 4.15/2.05  #Partial instantiations: 0
% 4.15/2.05  #Strategies tried      : 1
% 4.15/2.05  
% 4.15/2.05  Timing (in seconds)
% 4.15/2.05  ----------------------
% 4.51/2.05  Preprocessing        : 0.56
% 4.51/2.05  Parsing              : 0.29
% 4.51/2.05  CNF conversion       : 0.05
% 4.51/2.05  Main loop            : 0.58
% 4.51/2.05  Inferencing          : 0.21
% 4.51/2.05  Reduction            : 0.19
% 4.51/2.05  Demodulation         : 0.13
% 4.51/2.05  BG Simplification    : 0.04
% 4.51/2.05  Subsumption          : 0.10
% 4.51/2.05  Abstraction          : 0.03
% 4.51/2.05  MUC search           : 0.00
% 4.51/2.05  Cooper               : 0.00
% 4.51/2.05  Total                : 1.19
% 4.51/2.05  Index Insertion      : 0.00
% 4.51/2.05  Index Deletion       : 0.00
% 4.51/2.05  Index Matching       : 0.00
% 4.51/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
