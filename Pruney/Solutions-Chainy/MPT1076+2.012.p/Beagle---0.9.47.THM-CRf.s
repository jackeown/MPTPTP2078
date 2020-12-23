%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:13 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 209 expanded)
%              Number of leaves         :   40 (  91 expanded)
%              Depth                    :   15
%              Number of atoms          :  243 ( 753 expanded)
%              Number of equality atoms :   35 (  86 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_164,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_40,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_95,plain,(
    ! [C_108,B_109,A_110] :
      ( v5_relat_1(C_108,B_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_107,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_95])).

tff(c_69,plain,(
    ! [C_100,A_101,B_102] :
      ( v1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_69])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_121,plain,(
    ! [C_116,A_117,B_118] :
      ( v4_relat_1(C_116,A_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_133,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_121])).

tff(c_184,plain,(
    ! [B_136,A_137] :
      ( k1_relat_1(B_136) = A_137
      | ~ v1_partfun1(B_136,A_137)
      | ~ v4_relat_1(B_136,A_137)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_190,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_184])).

tff(c_196,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_190])).

tff(c_206,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_224,plain,(
    ! [C_146,A_147,B_148] :
      ( v1_partfun1(C_146,A_147)
      | ~ v1_funct_2(C_146,A_147,B_148)
      | ~ v1_funct_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148)))
      | v1_xboole_0(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_231,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_224])).

tff(c_238,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_231])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_206,c_238])).

tff(c_241,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_253,plain,(
    ! [B_149,A_150] :
      ( r2_hidden(k1_funct_1(B_149,A_150),k2_relat_1(B_149))
      | ~ r2_hidden(A_150,k1_relat_1(B_149))
      | ~ v1_funct_1(B_149)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_166,plain,(
    ! [A_124,C_125,B_126] :
      ( m1_subset_1(A_124,C_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(C_125))
      | ~ r2_hidden(A_124,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_173,plain,(
    ! [A_124,B_4,A_3] :
      ( m1_subset_1(A_124,B_4)
      | ~ r2_hidden(A_124,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_393,plain,(
    ! [B_188,A_189,B_190] :
      ( m1_subset_1(k1_funct_1(B_188,A_189),B_190)
      | ~ r1_tarski(k2_relat_1(B_188),B_190)
      | ~ r2_hidden(A_189,k1_relat_1(B_188))
      | ~ v1_funct_1(B_188)
      | ~ v1_relat_1(B_188) ) ),
    inference(resolution,[status(thm)],[c_253,c_173])).

tff(c_397,plain,(
    ! [B_191,A_192,A_193] :
      ( m1_subset_1(k1_funct_1(B_191,A_192),A_193)
      | ~ r2_hidden(A_192,k1_relat_1(B_191))
      | ~ v1_funct_1(B_191)
      | ~ v5_relat_1(B_191,A_193)
      | ~ v1_relat_1(B_191) ) ),
    inference(resolution,[status(thm)],[c_12,c_393])).

tff(c_399,plain,(
    ! [A_192,A_193] :
      ( m1_subset_1(k1_funct_1('#skF_4',A_192),A_193)
      | ~ r2_hidden(A_192,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_193)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_397])).

tff(c_410,plain,(
    ! [A_194,A_195] :
      ( m1_subset_1(k1_funct_1('#skF_4',A_194),A_195)
      | ~ r2_hidden(A_194,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_50,c_399])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_108,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_95])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_38,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_134,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_187,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_134,c_184])).

tff(c_193,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_38,c_187])).

tff(c_291,plain,(
    ! [A_166,B_167,C_168] :
      ( k7_partfun1(A_166,B_167,C_168) = k1_funct_1(B_167,C_168)
      | ~ r2_hidden(C_168,k1_relat_1(B_167))
      | ~ v1_funct_1(B_167)
      | ~ v5_relat_1(B_167,A_166)
      | ~ v1_relat_1(B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_295,plain,(
    ! [A_166,C_168] :
      ( k7_partfun1(A_166,'#skF_5',C_168) = k1_funct_1('#skF_5',C_168)
      | ~ r2_hidden(C_168,'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_166)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_291])).

tff(c_311,plain,(
    ! [A_171,C_172] :
      ( k7_partfun1(A_171,'#skF_5',C_172) = k1_funct_1('#skF_5',C_172)
      | ~ r2_hidden(C_172,'#skF_1')
      | ~ v5_relat_1('#skF_5',A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_44,c_295])).

tff(c_314,plain,(
    ! [A_171,A_1] :
      ( k7_partfun1(A_171,'#skF_5',A_1) = k1_funct_1('#skF_5',A_1)
      | ~ v5_relat_1('#skF_5',A_171)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_1,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2,c_311])).

tff(c_352,plain,(
    ! [A_180,A_181] :
      ( k7_partfun1(A_180,'#skF_5',A_181) = k1_funct_1('#skF_5',A_181)
      | ~ v5_relat_1('#skF_5',A_180)
      | ~ m1_subset_1(A_181,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_314])).

tff(c_355,plain,(
    ! [A_181] :
      ( k7_partfun1('#skF_3','#skF_5',A_181) = k1_funct_1('#skF_5',A_181)
      | ~ m1_subset_1(A_181,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_108,c_352])).

tff(c_418,plain,(
    ! [A_194] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',A_194)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_194))
      | ~ r2_hidden(A_194,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_410,c_355])).

tff(c_454,plain,(
    ! [A_194] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',A_194)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_194))
      | ~ r2_hidden(A_194,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_418])).

tff(c_331,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( k3_funct_2(A_176,B_177,C_178,D_179) = k1_funct_1(C_178,D_179)
      | ~ m1_subset_1(D_179,A_176)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_2(C_178,A_176,B_177)
      | ~ v1_funct_1(C_178)
      | v1_xboole_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_343,plain,(
    ! [B_177,C_178] :
      ( k3_funct_2('#skF_2',B_177,C_178,'#skF_6') = k1_funct_1(C_178,'#skF_6')
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_177)))
      | ~ v1_funct_2(C_178,'#skF_2',B_177)
      | ~ v1_funct_1(C_178)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_331])).

tff(c_376,plain,(
    ! [B_186,C_187] :
      ( k3_funct_2('#skF_2',B_186,C_187,'#skF_6') = k1_funct_1(C_187,'#skF_6')
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_186)))
      | ~ v1_funct_2(C_187,'#skF_2',B_186)
      | ~ v1_funct_1(C_187) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_343])).

tff(c_383,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_376])).

tff(c_387,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_383])).

tff(c_464,plain,(
    ! [A_197,B_196,E_199,F_198,D_200,C_201] :
      ( k3_funct_2(B_196,C_201,k8_funct_2(B_196,A_197,C_201,D_200,E_199),F_198) = k1_funct_1(E_199,k3_funct_2(B_196,A_197,D_200,F_198))
      | ~ v1_partfun1(E_199,A_197)
      | ~ m1_subset_1(F_198,B_196)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(A_197,C_201)))
      | ~ v1_funct_1(E_199)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(B_196,A_197)))
      | ~ v1_funct_2(D_200,B_196,A_197)
      | ~ v1_funct_1(D_200)
      | v1_xboole_0(B_196)
      | v1_xboole_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_474,plain,(
    ! [B_196,D_200,F_198] :
      ( k3_funct_2(B_196,'#skF_3',k8_funct_2(B_196,'#skF_1','#skF_3',D_200,'#skF_5'),F_198) = k1_funct_1('#skF_5',k3_funct_2(B_196,'#skF_1',D_200,F_198))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_198,B_196)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(B_196,'#skF_1')))
      | ~ v1_funct_2(D_200,B_196,'#skF_1')
      | ~ v1_funct_1(D_200)
      | v1_xboole_0(B_196)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_464])).

tff(c_483,plain,(
    ! [B_196,D_200,F_198] :
      ( k3_funct_2(B_196,'#skF_3',k8_funct_2(B_196,'#skF_1','#skF_3',D_200,'#skF_5'),F_198) = k1_funct_1('#skF_5',k3_funct_2(B_196,'#skF_1',D_200,F_198))
      | ~ m1_subset_1(F_198,B_196)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(B_196,'#skF_1')))
      | ~ v1_funct_2(D_200,B_196,'#skF_1')
      | ~ v1_funct_1(D_200)
      | v1_xboole_0(B_196)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_474])).

tff(c_561,plain,(
    ! [B_215,D_216,F_217] :
      ( k3_funct_2(B_215,'#skF_3',k8_funct_2(B_215,'#skF_1','#skF_3',D_216,'#skF_5'),F_217) = k1_funct_1('#skF_5',k3_funct_2(B_215,'#skF_1',D_216,F_217))
      | ~ m1_subset_1(F_217,B_215)
      | ~ m1_subset_1(D_216,k1_zfmisc_1(k2_zfmisc_1(B_215,'#skF_1')))
      | ~ v1_funct_2(D_216,B_215,'#skF_1')
      | ~ v1_funct_1(D_216)
      | v1_xboole_0(B_215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_483])).

tff(c_572,plain,(
    ! [F_217] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_217) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_217))
      | ~ m1_subset_1(F_217,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_561])).

tff(c_578,plain,(
    ! [F_217] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_217) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_217))
      | ~ m1_subset_1(F_217,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_572])).

tff(c_614,plain,(
    ! [F_229] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_229) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_229))
      | ~ m1_subset_1(F_229,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_578])).

tff(c_36,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_388,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_36])).

tff(c_620,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_388])).

tff(c_626,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_387,c_620])).

tff(c_631,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_626])).

tff(c_634,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_631])).

tff(c_637,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_634])).

tff(c_639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:27:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.52  
% 3.20/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.20/1.52  
% 3.20/1.52  %Foreground sorts:
% 3.20/1.52  
% 3.20/1.52  
% 3.20/1.52  %Background operators:
% 3.20/1.52  
% 3.20/1.52  
% 3.20/1.52  %Foreground operators:
% 3.20/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.52  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.20/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.52  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.52  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.20/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.20/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.20/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.52  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.20/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.52  
% 3.27/1.55  tff(f_164, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 3.27/1.55  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.27/1.55  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.27/1.55  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.27/1.55  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.27/1.55  tff(f_79, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.27/1.55  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.27/1.55  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.27/1.55  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.27/1.55  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.27/1.55  tff(f_98, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.27/1.55  tff(f_111, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.27/1.55  tff(f_137, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 3.27/1.55  tff(c_52, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.27/1.55  tff(c_40, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.27/1.55  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.55  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.27/1.55  tff(c_95, plain, (![C_108, B_109, A_110]: (v5_relat_1(C_108, B_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.55  tff(c_107, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_95])).
% 3.27/1.55  tff(c_69, plain, (![C_100, A_101, B_102]: (v1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.27/1.55  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_69])).
% 3.27/1.55  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.27/1.55  tff(c_54, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.27/1.55  tff(c_121, plain, (![C_116, A_117, B_118]: (v4_relat_1(C_116, A_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.55  tff(c_133, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_121])).
% 3.27/1.55  tff(c_184, plain, (![B_136, A_137]: (k1_relat_1(B_136)=A_137 | ~v1_partfun1(B_136, A_137) | ~v4_relat_1(B_136, A_137) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.27/1.55  tff(c_190, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_184])).
% 3.27/1.55  tff(c_196, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_190])).
% 3.27/1.55  tff(c_206, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_196])).
% 3.27/1.55  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.27/1.55  tff(c_224, plain, (![C_146, A_147, B_148]: (v1_partfun1(C_146, A_147) | ~v1_funct_2(C_146, A_147, B_148) | ~v1_funct_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))) | v1_xboole_0(B_148))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.27/1.55  tff(c_231, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_224])).
% 3.27/1.55  tff(c_238, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_231])).
% 3.27/1.55  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_206, c_238])).
% 3.27/1.55  tff(c_241, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_196])).
% 3.27/1.55  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.55  tff(c_253, plain, (![B_149, A_150]: (r2_hidden(k1_funct_1(B_149, A_150), k2_relat_1(B_149)) | ~r2_hidden(A_150, k1_relat_1(B_149)) | ~v1_funct_1(B_149) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.27/1.55  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.55  tff(c_166, plain, (![A_124, C_125, B_126]: (m1_subset_1(A_124, C_125) | ~m1_subset_1(B_126, k1_zfmisc_1(C_125)) | ~r2_hidden(A_124, B_126))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.55  tff(c_173, plain, (![A_124, B_4, A_3]: (m1_subset_1(A_124, B_4) | ~r2_hidden(A_124, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_166])).
% 3.27/1.55  tff(c_393, plain, (![B_188, A_189, B_190]: (m1_subset_1(k1_funct_1(B_188, A_189), B_190) | ~r1_tarski(k2_relat_1(B_188), B_190) | ~r2_hidden(A_189, k1_relat_1(B_188)) | ~v1_funct_1(B_188) | ~v1_relat_1(B_188))), inference(resolution, [status(thm)], [c_253, c_173])).
% 3.27/1.55  tff(c_397, plain, (![B_191, A_192, A_193]: (m1_subset_1(k1_funct_1(B_191, A_192), A_193) | ~r2_hidden(A_192, k1_relat_1(B_191)) | ~v1_funct_1(B_191) | ~v5_relat_1(B_191, A_193) | ~v1_relat_1(B_191))), inference(resolution, [status(thm)], [c_12, c_393])).
% 3.27/1.55  tff(c_399, plain, (![A_192, A_193]: (m1_subset_1(k1_funct_1('#skF_4', A_192), A_193) | ~r2_hidden(A_192, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_193) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_397])).
% 3.27/1.55  tff(c_410, plain, (![A_194, A_195]: (m1_subset_1(k1_funct_1('#skF_4', A_194), A_195) | ~r2_hidden(A_194, '#skF_2') | ~v5_relat_1('#skF_4', A_195))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_50, c_399])).
% 3.27/1.55  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.27/1.55  tff(c_108, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_95])).
% 3.27/1.55  tff(c_82, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_69])).
% 3.27/1.55  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.27/1.55  tff(c_38, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.27/1.55  tff(c_134, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_121])).
% 3.27/1.55  tff(c_187, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_134, c_184])).
% 3.27/1.55  tff(c_193, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_38, c_187])).
% 3.27/1.55  tff(c_291, plain, (![A_166, B_167, C_168]: (k7_partfun1(A_166, B_167, C_168)=k1_funct_1(B_167, C_168) | ~r2_hidden(C_168, k1_relat_1(B_167)) | ~v1_funct_1(B_167) | ~v5_relat_1(B_167, A_166) | ~v1_relat_1(B_167))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.27/1.55  tff(c_295, plain, (![A_166, C_168]: (k7_partfun1(A_166, '#skF_5', C_168)=k1_funct_1('#skF_5', C_168) | ~r2_hidden(C_168, '#skF_1') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_166) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_291])).
% 3.27/1.55  tff(c_311, plain, (![A_171, C_172]: (k7_partfun1(A_171, '#skF_5', C_172)=k1_funct_1('#skF_5', C_172) | ~r2_hidden(C_172, '#skF_1') | ~v5_relat_1('#skF_5', A_171))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_44, c_295])).
% 3.27/1.55  tff(c_314, plain, (![A_171, A_1]: (k7_partfun1(A_171, '#skF_5', A_1)=k1_funct_1('#skF_5', A_1) | ~v5_relat_1('#skF_5', A_171) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_1, '#skF_1'))), inference(resolution, [status(thm)], [c_2, c_311])).
% 3.27/1.55  tff(c_352, plain, (![A_180, A_181]: (k7_partfun1(A_180, '#skF_5', A_181)=k1_funct_1('#skF_5', A_181) | ~v5_relat_1('#skF_5', A_180) | ~m1_subset_1(A_181, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_314])).
% 3.27/1.55  tff(c_355, plain, (![A_181]: (k7_partfun1('#skF_3', '#skF_5', A_181)=k1_funct_1('#skF_5', A_181) | ~m1_subset_1(A_181, '#skF_1'))), inference(resolution, [status(thm)], [c_108, c_352])).
% 3.27/1.55  tff(c_418, plain, (![A_194]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', A_194))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_194)) | ~r2_hidden(A_194, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_410, c_355])).
% 3.27/1.55  tff(c_454, plain, (![A_194]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', A_194))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_194)) | ~r2_hidden(A_194, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_418])).
% 3.27/1.55  tff(c_331, plain, (![A_176, B_177, C_178, D_179]: (k3_funct_2(A_176, B_177, C_178, D_179)=k1_funct_1(C_178, D_179) | ~m1_subset_1(D_179, A_176) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_2(C_178, A_176, B_177) | ~v1_funct_1(C_178) | v1_xboole_0(A_176))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.27/1.55  tff(c_343, plain, (![B_177, C_178]: (k3_funct_2('#skF_2', B_177, C_178, '#skF_6')=k1_funct_1(C_178, '#skF_6') | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_177))) | ~v1_funct_2(C_178, '#skF_2', B_177) | ~v1_funct_1(C_178) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_331])).
% 3.27/1.55  tff(c_376, plain, (![B_186, C_187]: (k3_funct_2('#skF_2', B_186, C_187, '#skF_6')=k1_funct_1(C_187, '#skF_6') | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_186))) | ~v1_funct_2(C_187, '#skF_2', B_186) | ~v1_funct_1(C_187))), inference(negUnitSimplification, [status(thm)], [c_52, c_343])).
% 3.27/1.55  tff(c_383, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_376])).
% 3.27/1.55  tff(c_387, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_383])).
% 3.27/1.55  tff(c_464, plain, (![A_197, B_196, E_199, F_198, D_200, C_201]: (k3_funct_2(B_196, C_201, k8_funct_2(B_196, A_197, C_201, D_200, E_199), F_198)=k1_funct_1(E_199, k3_funct_2(B_196, A_197, D_200, F_198)) | ~v1_partfun1(E_199, A_197) | ~m1_subset_1(F_198, B_196) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(A_197, C_201))) | ~v1_funct_1(E_199) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(B_196, A_197))) | ~v1_funct_2(D_200, B_196, A_197) | ~v1_funct_1(D_200) | v1_xboole_0(B_196) | v1_xboole_0(A_197))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.27/1.55  tff(c_474, plain, (![B_196, D_200, F_198]: (k3_funct_2(B_196, '#skF_3', k8_funct_2(B_196, '#skF_1', '#skF_3', D_200, '#skF_5'), F_198)=k1_funct_1('#skF_5', k3_funct_2(B_196, '#skF_1', D_200, F_198)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_198, B_196) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(B_196, '#skF_1'))) | ~v1_funct_2(D_200, B_196, '#skF_1') | ~v1_funct_1(D_200) | v1_xboole_0(B_196) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_464])).
% 3.27/1.55  tff(c_483, plain, (![B_196, D_200, F_198]: (k3_funct_2(B_196, '#skF_3', k8_funct_2(B_196, '#skF_1', '#skF_3', D_200, '#skF_5'), F_198)=k1_funct_1('#skF_5', k3_funct_2(B_196, '#skF_1', D_200, F_198)) | ~m1_subset_1(F_198, B_196) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(B_196, '#skF_1'))) | ~v1_funct_2(D_200, B_196, '#skF_1') | ~v1_funct_1(D_200) | v1_xboole_0(B_196) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_474])).
% 3.27/1.55  tff(c_561, plain, (![B_215, D_216, F_217]: (k3_funct_2(B_215, '#skF_3', k8_funct_2(B_215, '#skF_1', '#skF_3', D_216, '#skF_5'), F_217)=k1_funct_1('#skF_5', k3_funct_2(B_215, '#skF_1', D_216, F_217)) | ~m1_subset_1(F_217, B_215) | ~m1_subset_1(D_216, k1_zfmisc_1(k2_zfmisc_1(B_215, '#skF_1'))) | ~v1_funct_2(D_216, B_215, '#skF_1') | ~v1_funct_1(D_216) | v1_xboole_0(B_215))), inference(negUnitSimplification, [status(thm)], [c_54, c_483])).
% 3.27/1.55  tff(c_572, plain, (![F_217]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_217)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_217)) | ~m1_subset_1(F_217, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_561])).
% 3.27/1.55  tff(c_578, plain, (![F_217]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_217)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_217)) | ~m1_subset_1(F_217, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_572])).
% 3.27/1.55  tff(c_614, plain, (![F_229]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_229)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_229)) | ~m1_subset_1(F_229, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_578])).
% 3.27/1.55  tff(c_36, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.27/1.55  tff(c_388, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_36])).
% 3.27/1.55  tff(c_620, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_614, c_388])).
% 3.27/1.55  tff(c_626, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_387, c_620])).
% 3.27/1.55  tff(c_631, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_454, c_626])).
% 3.27/1.55  tff(c_634, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_631])).
% 3.27/1.55  tff(c_637, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_634])).
% 3.27/1.55  tff(c_639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_637])).
% 3.27/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.55  
% 3.27/1.55  Inference rules
% 3.27/1.55  ----------------------
% 3.27/1.55  #Ref     : 0
% 3.27/1.55  #Sup     : 120
% 3.27/1.55  #Fact    : 0
% 3.27/1.55  #Define  : 0
% 3.27/1.55  #Split   : 10
% 3.27/1.55  #Chain   : 0
% 3.27/1.55  #Close   : 0
% 3.27/1.55  
% 3.27/1.55  Ordering : KBO
% 3.27/1.55  
% 3.27/1.55  Simplification rules
% 3.27/1.55  ----------------------
% 3.27/1.55  #Subsume      : 10
% 3.27/1.55  #Demod        : 58
% 3.27/1.55  #Tautology    : 27
% 3.27/1.55  #SimpNegUnit  : 12
% 3.27/1.55  #BackRed      : 1
% 3.27/1.55  
% 3.27/1.55  #Partial instantiations: 0
% 3.27/1.55  #Strategies tried      : 1
% 3.27/1.55  
% 3.27/1.55  Timing (in seconds)
% 3.27/1.55  ----------------------
% 3.27/1.55  Preprocessing        : 0.35
% 3.27/1.55  Parsing              : 0.18
% 3.27/1.55  CNF conversion       : 0.03
% 3.27/1.55  Main loop            : 0.40
% 3.27/1.55  Inferencing          : 0.16
% 3.27/1.55  Reduction            : 0.12
% 3.27/1.55  Demodulation         : 0.08
% 3.27/1.55  BG Simplification    : 0.02
% 3.27/1.55  Subsumption          : 0.06
% 3.27/1.55  Abstraction          : 0.02
% 3.27/1.55  MUC search           : 0.00
% 3.27/1.55  Cooper               : 0.00
% 3.27/1.55  Total                : 0.80
% 3.27/1.55  Index Insertion      : 0.00
% 3.27/1.55  Index Deletion       : 0.00
% 3.27/1.55  Index Matching       : 0.00
% 3.27/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
