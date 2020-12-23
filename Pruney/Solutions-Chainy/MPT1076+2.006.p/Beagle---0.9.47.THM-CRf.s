%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:12 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 259 expanded)
%              Number of leaves         :   38 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  266 ( 989 expanded)
%              Number of equality atoms :   35 ( 104 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k7_partfun1(C,E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,A)
                 => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_157,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C,D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
             => ! [E] :
                  ( ( v1_funct_1(E)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                 => ! [F] :
                      ( m1_subset_1(F,B)
                     => ( v1_partfun1(E,A)
                       => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_38,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_36,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_203,plain,(
    ! [C_143,A_144,B_145] :
      ( ~ v1_partfun1(C_143,A_144)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_xboole_0(B_145)
      | v1_xboole_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_209,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_203])).

tff(c_216,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_209])).

tff(c_217,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_216])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_68,plain,(
    ! [C_116,B_117,A_118] :
      ( v5_relat_1(C_116,B_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_75,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_218,plain,(
    ! [C_146,A_147,B_148] :
      ( v1_funct_2(C_146,A_147,B_148)
      | ~ v1_partfun1(C_146,A_147)
      | ~ v1_funct_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_224,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_218])).

tff(c_230,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_224])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    ! [B_112,A_113] :
      ( v1_relat_1(B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_113))
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_54])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_77,plain,(
    ! [C_119,A_120,B_121] :
      ( v4_relat_1(C_119,A_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_84,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_77])).

tff(c_87,plain,(
    ! [B_123,A_124] :
      ( k1_relat_1(B_123) = A_124
      | ~ v1_partfun1(B_123,A_124)
      | ~ v4_relat_1(B_123,A_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_93,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_87])).

tff(c_99,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_93])).

tff(c_109,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_174,plain,(
    ! [C_140,A_141,B_142] :
      ( v1_partfun1(C_140,A_141)
      | ~ v1_funct_2(C_140,A_141,B_142)
      | ~ v1_funct_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | v1_xboole_0(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_181,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_174])).

tff(c_188,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_181])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_109,c_188])).

tff(c_191,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_231,plain,(
    ! [C_149,B_150,A_151] :
      ( m1_subset_1(k1_funct_1(C_149,B_150),A_151)
      | ~ r2_hidden(B_150,k1_relat_1(C_149))
      | ~ v1_funct_1(C_149)
      | ~ v5_relat_1(C_149,A_151)
      | ~ v1_relat_1(C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_233,plain,(
    ! [B_150,A_151] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_150),A_151)
      | ~ r2_hidden(B_150,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_151)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_231])).

tff(c_240,plain,(
    ! [B_150,A_151] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_150),A_151)
      | ~ r2_hidden(B_150,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_233])).

tff(c_413,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( k3_funct_2(A_199,B_200,C_201,D_202) = k7_partfun1(B_200,C_201,D_202)
      | ~ m1_subset_1(D_202,A_199)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_2(C_201,A_199,B_200)
      | ~ v1_funct_1(C_201)
      | v1_xboole_0(B_200)
      | v1_xboole_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_608,plain,(
    ! [A_259,B_260,C_261,B_262] :
      ( k3_funct_2(A_259,B_260,C_261,k1_funct_1('#skF_4',B_262)) = k7_partfun1(B_260,C_261,k1_funct_1('#skF_4',B_262))
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260)))
      | ~ v1_funct_2(C_261,A_259,B_260)
      | ~ v1_funct_1(C_261)
      | v1_xboole_0(B_260)
      | v1_xboole_0(A_259)
      | ~ r2_hidden(B_262,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_259) ) ),
    inference(resolution,[status(thm)],[c_240,c_413])).

tff(c_621,plain,(
    ! [B_262] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_262)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_262))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_262,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_608])).

tff(c_631,plain,(
    ! [B_262] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_262)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_262))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_262,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_230,c_621])).

tff(c_633,plain,(
    ! [B_263] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_263)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_263))
      | ~ r2_hidden(B_263,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_217,c_631])).

tff(c_329,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( k3_funct_2(A_173,B_174,C_175,D_176) = k1_funct_1(C_175,D_176)
      | ~ m1_subset_1(D_176,A_173)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_2(C_175,A_173,B_174)
      | ~ v1_funct_1(C_175)
      | v1_xboole_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_569,plain,(
    ! [A_246,B_247,C_248,B_249] :
      ( k3_funct_2(A_246,B_247,C_248,k1_funct_1('#skF_4',B_249)) = k1_funct_1(C_248,k1_funct_1('#skF_4',B_249))
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ v1_funct_2(C_248,A_246,B_247)
      | ~ v1_funct_1(C_248)
      | v1_xboole_0(A_246)
      | ~ r2_hidden(B_249,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_246) ) ),
    inference(resolution,[status(thm)],[c_240,c_329])).

tff(c_582,plain,(
    ! [B_249] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_249)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_249))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_249,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_569])).

tff(c_592,plain,(
    ! [B_249] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_249)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_249))
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_249,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_230,c_582])).

tff(c_593,plain,(
    ! [B_249] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_249)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_249))
      | ~ r2_hidden(B_249,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_592])).

tff(c_648,plain,(
    ! [B_264] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_264)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_264))
      | ~ r2_hidden(B_264,'#skF_2')
      | ~ r2_hidden(B_264,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_593])).

tff(c_339,plain,(
    ! [B_174,C_175] :
      ( k3_funct_2('#skF_2',B_174,C_175,'#skF_6') = k1_funct_1(C_175,'#skF_6')
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_174)))
      | ~ v1_funct_2(C_175,'#skF_2',B_174)
      | ~ v1_funct_1(C_175)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_329])).

tff(c_383,plain,(
    ! [B_186,C_187] :
      ( k3_funct_2('#skF_2',B_186,C_187,'#skF_6') = k1_funct_1(C_187,'#skF_6')
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_186)))
      | ~ v1_funct_2(C_187,'#skF_2',B_186)
      | ~ v1_funct_1(C_187) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_339])).

tff(c_398,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_383])).

tff(c_404,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_398])).

tff(c_467,plain,(
    ! [B_222,C_225,F_221,E_223,D_224,A_226] :
      ( k3_funct_2(B_222,C_225,k8_funct_2(B_222,A_226,C_225,D_224,E_223),F_221) = k1_funct_1(E_223,k3_funct_2(B_222,A_226,D_224,F_221))
      | ~ v1_partfun1(E_223,A_226)
      | ~ m1_subset_1(F_221,B_222)
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(A_226,C_225)))
      | ~ v1_funct_1(E_223)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(B_222,A_226)))
      | ~ v1_funct_2(D_224,B_222,A_226)
      | ~ v1_funct_1(D_224)
      | v1_xboole_0(B_222)
      | v1_xboole_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_480,plain,(
    ! [B_222,D_224,F_221] :
      ( k3_funct_2(B_222,'#skF_3',k8_funct_2(B_222,'#skF_1','#skF_3',D_224,'#skF_5'),F_221) = k1_funct_1('#skF_5',k3_funct_2(B_222,'#skF_1',D_224,F_221))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_221,B_222)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(B_222,'#skF_1')))
      | ~ v1_funct_2(D_224,B_222,'#skF_1')
      | ~ v1_funct_1(D_224)
      | v1_xboole_0(B_222)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_467])).

tff(c_490,plain,(
    ! [B_222,D_224,F_221] :
      ( k3_funct_2(B_222,'#skF_3',k8_funct_2(B_222,'#skF_1','#skF_3',D_224,'#skF_5'),F_221) = k1_funct_1('#skF_5',k3_funct_2(B_222,'#skF_1',D_224,F_221))
      | ~ m1_subset_1(F_221,B_222)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(B_222,'#skF_1')))
      | ~ v1_funct_2(D_224,B_222,'#skF_1')
      | ~ v1_funct_1(D_224)
      | v1_xboole_0(B_222)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_480])).

tff(c_495,plain,(
    ! [B_235,D_236,F_237] :
      ( k3_funct_2(B_235,'#skF_3',k8_funct_2(B_235,'#skF_1','#skF_3',D_236,'#skF_5'),F_237) = k1_funct_1('#skF_5',k3_funct_2(B_235,'#skF_1',D_236,F_237))
      | ~ m1_subset_1(F_237,B_235)
      | ~ m1_subset_1(D_236,k1_zfmisc_1(k2_zfmisc_1(B_235,'#skF_1')))
      | ~ v1_funct_2(D_236,B_235,'#skF_1')
      | ~ v1_funct_1(D_236)
      | v1_xboole_0(B_235) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_490])).

tff(c_506,plain,(
    ! [F_237] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_237) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_237))
      | ~ m1_subset_1(F_237,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_495])).

tff(c_512,plain,(
    ! [F_237] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_237) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_237))
      | ~ m1_subset_1(F_237,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_506])).

tff(c_514,plain,(
    ! [F_238] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_238) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_238))
      | ~ m1_subset_1(F_238,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_512])).

tff(c_34,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_405,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_34])).

tff(c_520,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_405])).

tff(c_526,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_404,c_520])).

tff(c_659,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_526])).

tff(c_663,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_659])).

tff(c_666,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_663])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.53  
% 3.40/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.40/1.54  
% 3.40/1.54  %Foreground sorts:
% 3.40/1.54  
% 3.40/1.54  
% 3.40/1.54  %Background operators:
% 3.40/1.54  
% 3.40/1.54  
% 3.40/1.54  %Foreground operators:
% 3.40/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.54  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.40/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.40/1.54  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.54  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.40/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.40/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.40/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.40/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.40/1.54  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.40/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.54  
% 3.56/1.56  tff(f_184, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 3.56/1.56  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.56/1.56  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 3.56/1.56  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.56/1.56  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.56/1.56  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.56/1.56  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.56/1.56  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.56/1.56  tff(f_91, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.56/1.56  tff(f_50, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 3.56/1.56  tff(f_131, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 3.56/1.56  tff(f_112, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.56/1.56  tff(f_157, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 3.56/1.56  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.56/1.56  tff(c_38, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.56/1.56  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.56  tff(c_52, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.56/1.56  tff(c_36, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.56/1.56  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.56/1.56  tff(c_203, plain, (![C_143, A_144, B_145]: (~v1_partfun1(C_143, A_144) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_xboole_0(B_145) | v1_xboole_0(A_144))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.56/1.56  tff(c_209, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_203])).
% 3.56/1.56  tff(c_216, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_209])).
% 3.56/1.56  tff(c_217, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_216])).
% 3.56/1.56  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.56/1.56  tff(c_68, plain, (![C_116, B_117, A_118]: (v5_relat_1(C_116, B_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.56  tff(c_75, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_68])).
% 3.56/1.56  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.56/1.56  tff(c_218, plain, (![C_146, A_147, B_148]: (v1_funct_2(C_146, A_147, B_148) | ~v1_partfun1(C_146, A_147) | ~v1_funct_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.56/1.56  tff(c_224, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_218])).
% 3.56/1.56  tff(c_230, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_224])).
% 3.56/1.56  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.56/1.56  tff(c_54, plain, (![B_112, A_113]: (v1_relat_1(B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(A_113)) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.56/1.56  tff(c_57, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_54])).
% 3.56/1.56  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_57])).
% 3.56/1.56  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.56/1.56  tff(c_77, plain, (![C_119, A_120, B_121]: (v4_relat_1(C_119, A_120) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.56  tff(c_84, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_77])).
% 3.56/1.56  tff(c_87, plain, (![B_123, A_124]: (k1_relat_1(B_123)=A_124 | ~v1_partfun1(B_123, A_124) | ~v4_relat_1(B_123, A_124) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.56/1.56  tff(c_93, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_87])).
% 3.56/1.56  tff(c_99, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_93])).
% 3.56/1.56  tff(c_109, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_99])).
% 3.56/1.56  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.56/1.56  tff(c_174, plain, (![C_140, A_141, B_142]: (v1_partfun1(C_140, A_141) | ~v1_funct_2(C_140, A_141, B_142) | ~v1_funct_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | v1_xboole_0(B_142))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.56/1.56  tff(c_181, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_174])).
% 3.56/1.56  tff(c_188, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_181])).
% 3.56/1.56  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_109, c_188])).
% 3.56/1.56  tff(c_191, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_99])).
% 3.56/1.56  tff(c_231, plain, (![C_149, B_150, A_151]: (m1_subset_1(k1_funct_1(C_149, B_150), A_151) | ~r2_hidden(B_150, k1_relat_1(C_149)) | ~v1_funct_1(C_149) | ~v5_relat_1(C_149, A_151) | ~v1_relat_1(C_149))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.56/1.56  tff(c_233, plain, (![B_150, A_151]: (m1_subset_1(k1_funct_1('#skF_4', B_150), A_151) | ~r2_hidden(B_150, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_151) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_231])).
% 3.56/1.56  tff(c_240, plain, (![B_150, A_151]: (m1_subset_1(k1_funct_1('#skF_4', B_150), A_151) | ~r2_hidden(B_150, '#skF_2') | ~v5_relat_1('#skF_4', A_151))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_233])).
% 3.56/1.56  tff(c_413, plain, (![A_199, B_200, C_201, D_202]: (k3_funct_2(A_199, B_200, C_201, D_202)=k7_partfun1(B_200, C_201, D_202) | ~m1_subset_1(D_202, A_199) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_2(C_201, A_199, B_200) | ~v1_funct_1(C_201) | v1_xboole_0(B_200) | v1_xboole_0(A_199))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.56/1.56  tff(c_608, plain, (![A_259, B_260, C_261, B_262]: (k3_funct_2(A_259, B_260, C_261, k1_funct_1('#skF_4', B_262))=k7_partfun1(B_260, C_261, k1_funct_1('#skF_4', B_262)) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))) | ~v1_funct_2(C_261, A_259, B_260) | ~v1_funct_1(C_261) | v1_xboole_0(B_260) | v1_xboole_0(A_259) | ~r2_hidden(B_262, '#skF_2') | ~v5_relat_1('#skF_4', A_259))), inference(resolution, [status(thm)], [c_240, c_413])).
% 3.56/1.56  tff(c_621, plain, (![B_262]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_262))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_262)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1') | ~r2_hidden(B_262, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_40, c_608])).
% 3.56/1.56  tff(c_631, plain, (![B_262]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_262))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_262)) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1') | ~r2_hidden(B_262, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_230, c_621])).
% 3.56/1.56  tff(c_633, plain, (![B_263]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_263))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_263)) | ~r2_hidden(B_263, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_217, c_631])).
% 3.56/1.56  tff(c_329, plain, (![A_173, B_174, C_175, D_176]: (k3_funct_2(A_173, B_174, C_175, D_176)=k1_funct_1(C_175, D_176) | ~m1_subset_1(D_176, A_173) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_2(C_175, A_173, B_174) | ~v1_funct_1(C_175) | v1_xboole_0(A_173))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.56/1.56  tff(c_569, plain, (![A_246, B_247, C_248, B_249]: (k3_funct_2(A_246, B_247, C_248, k1_funct_1('#skF_4', B_249))=k1_funct_1(C_248, k1_funct_1('#skF_4', B_249)) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))) | ~v1_funct_2(C_248, A_246, B_247) | ~v1_funct_1(C_248) | v1_xboole_0(A_246) | ~r2_hidden(B_249, '#skF_2') | ~v5_relat_1('#skF_4', A_246))), inference(resolution, [status(thm)], [c_240, c_329])).
% 3.56/1.56  tff(c_582, plain, (![B_249]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_249))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_249)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_1') | ~r2_hidden(B_249, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_40, c_569])).
% 3.56/1.56  tff(c_592, plain, (![B_249]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_249))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_249)) | v1_xboole_0('#skF_1') | ~r2_hidden(B_249, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_230, c_582])).
% 3.56/1.56  tff(c_593, plain, (![B_249]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_249))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_249)) | ~r2_hidden(B_249, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_592])).
% 3.56/1.56  tff(c_648, plain, (![B_264]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_264))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_264)) | ~r2_hidden(B_264, '#skF_2') | ~r2_hidden(B_264, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_633, c_593])).
% 3.56/1.56  tff(c_339, plain, (![B_174, C_175]: (k3_funct_2('#skF_2', B_174, C_175, '#skF_6')=k1_funct_1(C_175, '#skF_6') | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_174))) | ~v1_funct_2(C_175, '#skF_2', B_174) | ~v1_funct_1(C_175) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_329])).
% 3.56/1.56  tff(c_383, plain, (![B_186, C_187]: (k3_funct_2('#skF_2', B_186, C_187, '#skF_6')=k1_funct_1(C_187, '#skF_6') | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_186))) | ~v1_funct_2(C_187, '#skF_2', B_186) | ~v1_funct_1(C_187))), inference(negUnitSimplification, [status(thm)], [c_50, c_339])).
% 3.56/1.56  tff(c_398, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_383])).
% 3.56/1.56  tff(c_404, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_398])).
% 3.56/1.56  tff(c_467, plain, (![B_222, C_225, F_221, E_223, D_224, A_226]: (k3_funct_2(B_222, C_225, k8_funct_2(B_222, A_226, C_225, D_224, E_223), F_221)=k1_funct_1(E_223, k3_funct_2(B_222, A_226, D_224, F_221)) | ~v1_partfun1(E_223, A_226) | ~m1_subset_1(F_221, B_222) | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(A_226, C_225))) | ~v1_funct_1(E_223) | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(B_222, A_226))) | ~v1_funct_2(D_224, B_222, A_226) | ~v1_funct_1(D_224) | v1_xboole_0(B_222) | v1_xboole_0(A_226))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.56/1.56  tff(c_480, plain, (![B_222, D_224, F_221]: (k3_funct_2(B_222, '#skF_3', k8_funct_2(B_222, '#skF_1', '#skF_3', D_224, '#skF_5'), F_221)=k1_funct_1('#skF_5', k3_funct_2(B_222, '#skF_1', D_224, F_221)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_221, B_222) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(B_222, '#skF_1'))) | ~v1_funct_2(D_224, B_222, '#skF_1') | ~v1_funct_1(D_224) | v1_xboole_0(B_222) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_467])).
% 3.56/1.56  tff(c_490, plain, (![B_222, D_224, F_221]: (k3_funct_2(B_222, '#skF_3', k8_funct_2(B_222, '#skF_1', '#skF_3', D_224, '#skF_5'), F_221)=k1_funct_1('#skF_5', k3_funct_2(B_222, '#skF_1', D_224, F_221)) | ~m1_subset_1(F_221, B_222) | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(B_222, '#skF_1'))) | ~v1_funct_2(D_224, B_222, '#skF_1') | ~v1_funct_1(D_224) | v1_xboole_0(B_222) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_480])).
% 3.56/1.56  tff(c_495, plain, (![B_235, D_236, F_237]: (k3_funct_2(B_235, '#skF_3', k8_funct_2(B_235, '#skF_1', '#skF_3', D_236, '#skF_5'), F_237)=k1_funct_1('#skF_5', k3_funct_2(B_235, '#skF_1', D_236, F_237)) | ~m1_subset_1(F_237, B_235) | ~m1_subset_1(D_236, k1_zfmisc_1(k2_zfmisc_1(B_235, '#skF_1'))) | ~v1_funct_2(D_236, B_235, '#skF_1') | ~v1_funct_1(D_236) | v1_xboole_0(B_235))), inference(negUnitSimplification, [status(thm)], [c_52, c_490])).
% 3.56/1.56  tff(c_506, plain, (![F_237]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_237)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_237)) | ~m1_subset_1(F_237, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_495])).
% 3.56/1.56  tff(c_512, plain, (![F_237]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_237)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_237)) | ~m1_subset_1(F_237, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_506])).
% 3.56/1.56  tff(c_514, plain, (![F_238]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_238)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_238)) | ~m1_subset_1(F_238, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_512])).
% 3.56/1.56  tff(c_34, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.56/1.56  tff(c_405, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_34])).
% 3.56/1.56  tff(c_520, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_514, c_405])).
% 3.56/1.56  tff(c_526, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_404, c_520])).
% 3.56/1.56  tff(c_659, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_648, c_526])).
% 3.56/1.56  tff(c_663, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_659])).
% 3.56/1.56  tff(c_666, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_663])).
% 3.56/1.56  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_666])).
% 3.56/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.56  
% 3.56/1.56  Inference rules
% 3.56/1.56  ----------------------
% 3.56/1.56  #Ref     : 0
% 3.56/1.56  #Sup     : 119
% 3.56/1.56  #Fact    : 0
% 3.56/1.56  #Define  : 0
% 3.56/1.56  #Split   : 9
% 3.56/1.56  #Chain   : 0
% 3.56/1.56  #Close   : 0
% 3.56/1.56  
% 3.56/1.56  Ordering : KBO
% 3.56/1.56  
% 3.56/1.56  Simplification rules
% 3.56/1.56  ----------------------
% 3.56/1.56  #Subsume      : 4
% 3.56/1.56  #Demod        : 69
% 3.56/1.56  #Tautology    : 24
% 3.56/1.56  #SimpNegUnit  : 20
% 3.56/1.56  #BackRed      : 1
% 3.56/1.56  
% 3.56/1.56  #Partial instantiations: 0
% 3.56/1.56  #Strategies tried      : 1
% 3.56/1.56  
% 3.56/1.56  Timing (in seconds)
% 3.56/1.56  ----------------------
% 3.56/1.56  Preprocessing        : 0.37
% 3.56/1.56  Parsing              : 0.19
% 3.56/1.56  CNF conversion       : 0.04
% 3.56/1.56  Main loop            : 0.41
% 3.56/1.56  Inferencing          : 0.15
% 3.56/1.56  Reduction            : 0.12
% 3.56/1.56  Demodulation         : 0.08
% 3.56/1.56  BG Simplification    : 0.02
% 3.56/1.56  Subsumption          : 0.08
% 3.56/1.56  Abstraction          : 0.02
% 3.56/1.56  MUC search           : 0.00
% 3.56/1.56  Cooper               : 0.00
% 3.56/1.56  Total                : 0.83
% 3.56/1.56  Index Insertion      : 0.00
% 3.56/1.56  Index Deletion       : 0.00
% 3.56/1.56  Index Matching       : 0.00
% 3.56/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
