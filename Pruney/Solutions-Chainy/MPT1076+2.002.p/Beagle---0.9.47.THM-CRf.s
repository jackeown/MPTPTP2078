%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:12 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 244 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   16
%              Number of atoms          :  260 ( 959 expanded)
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

tff(f_179,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_126,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_152,axiom,(
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

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_36,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_34,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_195,plain,(
    ! [C_138,A_139,B_140] :
      ( ~ v1_partfun1(C_138,A_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_xboole_0(B_140)
      | v1_xboole_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_201,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_195])).

tff(c_208,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_201])).

tff(c_209,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_208])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_70,plain,(
    ! [C_116,B_117,A_118] :
      ( v5_relat_1(C_116,B_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_77,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_210,plain,(
    ! [C_141,A_142,B_143] :
      ( v1_funct_2(C_141,A_142,B_143)
      | ~ v1_partfun1(C_141,A_142)
      | ~ v1_funct_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_216,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_210])).

tff(c_222,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_216])).

tff(c_52,plain,(
    ! [C_110,A_111,B_112] :
      ( v1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_59,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_52])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_61,plain,(
    ! [C_113,A_114,B_115] :
      ( v4_relat_1(C_113,A_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_61])).

tff(c_80,plain,(
    ! [B_120,A_121] :
      ( k1_relat_1(B_120) = A_121
      | ~ v1_partfun1(B_120,A_121)
      | ~ v4_relat_1(B_120,A_121)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_86,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_80])).

tff(c_92,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_86])).

tff(c_102,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_166,plain,(
    ! [C_135,A_136,B_137] :
      ( v1_partfun1(C_135,A_136)
      | ~ v1_funct_2(C_135,A_136,B_137)
      | ~ v1_funct_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | v1_xboole_0(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_173,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_166])).

tff(c_180,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_173])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_102,c_180])).

tff(c_183,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_223,plain,(
    ! [C_144,B_145,A_146] :
      ( m1_subset_1(k1_funct_1(C_144,B_145),A_146)
      | ~ r2_hidden(B_145,k1_relat_1(C_144))
      | ~ v1_funct_1(C_144)
      | ~ v5_relat_1(C_144,A_146)
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_225,plain,(
    ! [B_145,A_146] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_145),A_146)
      | ~ r2_hidden(B_145,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_146)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_223])).

tff(c_232,plain,(
    ! [B_145,A_146] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_145),A_146)
      | ~ r2_hidden(B_145,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_46,c_225])).

tff(c_399,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( k3_funct_2(A_179,B_180,C_181,D_182) = k7_partfun1(B_180,C_181,D_182)
      | ~ m1_subset_1(D_182,A_179)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_2(C_181,A_179,B_180)
      | ~ v1_funct_1(C_181)
      | v1_xboole_0(B_180)
      | v1_xboole_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_585,plain,(
    ! [A_219,B_220,C_221,B_222] :
      ( k3_funct_2(A_219,B_220,C_221,k1_funct_1('#skF_4',B_222)) = k7_partfun1(B_220,C_221,k1_funct_1('#skF_4',B_222))
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ v1_funct_2(C_221,A_219,B_220)
      | ~ v1_funct_1(C_221)
      | v1_xboole_0(B_220)
      | v1_xboole_0(A_219)
      | ~ r2_hidden(B_222,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_219) ) ),
    inference(resolution,[status(thm)],[c_232,c_399])).

tff(c_598,plain,(
    ! [B_222] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_222)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_222))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_222,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_585])).

tff(c_608,plain,(
    ! [B_222] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_222)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_222))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_222,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_40,c_222,c_598])).

tff(c_610,plain,(
    ! [B_223] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_223)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_223))
      | ~ r2_hidden(B_223,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_209,c_608])).

tff(c_317,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k3_funct_2(A_158,B_159,C_160,D_161) = k1_funct_1(C_160,D_161)
      | ~ m1_subset_1(D_161,A_158)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_2(C_160,A_158,B_159)
      | ~ v1_funct_1(C_160)
      | v1_xboole_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_475,plain,(
    ! [A_199,B_200,C_201,B_202] :
      ( k3_funct_2(A_199,B_200,C_201,k1_funct_1('#skF_4',B_202)) = k1_funct_1(C_201,k1_funct_1('#skF_4',B_202))
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_2(C_201,A_199,B_200)
      | ~ v1_funct_1(C_201)
      | v1_xboole_0(A_199)
      | ~ r2_hidden(B_202,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_199) ) ),
    inference(resolution,[status(thm)],[c_232,c_317])).

tff(c_488,plain,(
    ! [B_202] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_202)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_202))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_202,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_475])).

tff(c_498,plain,(
    ! [B_202] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_202)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_202))
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_202,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_40,c_222,c_488])).

tff(c_499,plain,(
    ! [B_202] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_202)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_202))
      | ~ r2_hidden(B_202,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_498])).

tff(c_626,plain,(
    ! [B_224] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_224)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_224))
      | ~ r2_hidden(B_224,'#skF_2')
      | ~ r2_hidden(B_224,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_499])).

tff(c_327,plain,(
    ! [B_159,C_160] :
      ( k3_funct_2('#skF_2',B_159,C_160,'#skF_6') = k1_funct_1(C_160,'#skF_6')
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_159)))
      | ~ v1_funct_2(C_160,'#skF_2',B_159)
      | ~ v1_funct_1(C_160)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_317])).

tff(c_369,plain,(
    ! [B_165,C_166] :
      ( k3_funct_2('#skF_2',B_165,C_166,'#skF_6') = k1_funct_1(C_166,'#skF_6')
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_165)))
      | ~ v1_funct_2(C_166,'#skF_2',B_165)
      | ~ v1_funct_1(C_166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_327])).

tff(c_384,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_369])).

tff(c_390,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_384])).

tff(c_449,plain,(
    ! [C_193,F_189,B_190,A_192,E_194,D_191] :
      ( k3_funct_2(B_190,C_193,k8_funct_2(B_190,A_192,C_193,D_191,E_194),F_189) = k1_funct_1(E_194,k3_funct_2(B_190,A_192,D_191,F_189))
      | ~ v1_partfun1(E_194,A_192)
      | ~ m1_subset_1(F_189,B_190)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_192,C_193)))
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1(D_191,k1_zfmisc_1(k2_zfmisc_1(B_190,A_192)))
      | ~ v1_funct_2(D_191,B_190,A_192)
      | ~ v1_funct_1(D_191)
      | v1_xboole_0(B_190)
      | v1_xboole_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_462,plain,(
    ! [B_190,D_191,F_189] :
      ( k3_funct_2(B_190,'#skF_3',k8_funct_2(B_190,'#skF_1','#skF_3',D_191,'#skF_5'),F_189) = k1_funct_1('#skF_5',k3_funct_2(B_190,'#skF_1',D_191,F_189))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_189,B_190)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_191,k1_zfmisc_1(k2_zfmisc_1(B_190,'#skF_1')))
      | ~ v1_funct_2(D_191,B_190,'#skF_1')
      | ~ v1_funct_1(D_191)
      | v1_xboole_0(B_190)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_449])).

tff(c_472,plain,(
    ! [B_190,D_191,F_189] :
      ( k3_funct_2(B_190,'#skF_3',k8_funct_2(B_190,'#skF_1','#skF_3',D_191,'#skF_5'),F_189) = k1_funct_1('#skF_5',k3_funct_2(B_190,'#skF_1',D_191,F_189))
      | ~ m1_subset_1(F_189,B_190)
      | ~ m1_subset_1(D_191,k1_zfmisc_1(k2_zfmisc_1(B_190,'#skF_1')))
      | ~ v1_funct_2(D_191,B_190,'#skF_1')
      | ~ v1_funct_1(D_191)
      | v1_xboole_0(B_190)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_462])).

tff(c_538,plain,(
    ! [B_208,D_209,F_210] :
      ( k3_funct_2(B_208,'#skF_3',k8_funct_2(B_208,'#skF_1','#skF_3',D_209,'#skF_5'),F_210) = k1_funct_1('#skF_5',k3_funct_2(B_208,'#skF_1',D_209,F_210))
      | ~ m1_subset_1(F_210,B_208)
      | ~ m1_subset_1(D_209,k1_zfmisc_1(k2_zfmisc_1(B_208,'#skF_1')))
      | ~ v1_funct_2(D_209,B_208,'#skF_1')
      | ~ v1_funct_1(D_209)
      | v1_xboole_0(B_208) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_472])).

tff(c_549,plain,(
    ! [F_210] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_210) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_210))
      | ~ m1_subset_1(F_210,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_538])).

tff(c_555,plain,(
    ! [F_210] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_210) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_210))
      | ~ m1_subset_1(F_210,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_549])).

tff(c_557,plain,(
    ! [F_211] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_211) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_211))
      | ~ m1_subset_1(F_211,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_555])).

tff(c_32,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_391,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_32])).

tff(c_563,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_391])).

tff(c_569,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_390,c_563])).

tff(c_637,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_569])).

tff(c_641,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_637])).

tff(c_644,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_641])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.86/1.45  
% 2.86/1.45  %Foreground sorts:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Background operators:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Foreground operators:
% 2.86/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.45  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.86/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.86/1.45  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.86/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.45  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.86/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.86/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.86/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.45  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.86/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.45  
% 3.19/1.47  tff(f_179, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 3.19/1.47  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.19/1.47  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 3.19/1.47  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.19/1.47  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.19/1.47  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.19/1.47  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.19/1.47  tff(f_86, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.19/1.47  tff(f_41, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 3.19/1.47  tff(f_126, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 3.19/1.47  tff(f_107, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.19/1.47  tff(f_152, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 3.19/1.47  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.19/1.47  tff(c_36, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.19/1.47  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.47  tff(c_50, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.19/1.47  tff(c_34, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.19/1.47  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.19/1.47  tff(c_195, plain, (![C_138, A_139, B_140]: (~v1_partfun1(C_138, A_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_xboole_0(B_140) | v1_xboole_0(A_139))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.19/1.47  tff(c_201, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_195])).
% 3.19/1.47  tff(c_208, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_201])).
% 3.19/1.47  tff(c_209, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_208])).
% 3.19/1.47  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.19/1.47  tff(c_70, plain, (![C_116, B_117, A_118]: (v5_relat_1(C_116, B_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.47  tff(c_77, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_70])).
% 3.19/1.47  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.19/1.47  tff(c_210, plain, (![C_141, A_142, B_143]: (v1_funct_2(C_141, A_142, B_143) | ~v1_partfun1(C_141, A_142) | ~v1_funct_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.47  tff(c_216, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_210])).
% 3.19/1.47  tff(c_222, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_216])).
% 3.19/1.47  tff(c_52, plain, (![C_110, A_111, B_112]: (v1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.19/1.47  tff(c_59, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_52])).
% 3.19/1.47  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.19/1.47  tff(c_61, plain, (![C_113, A_114, B_115]: (v4_relat_1(C_113, A_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.47  tff(c_68, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_61])).
% 3.19/1.47  tff(c_80, plain, (![B_120, A_121]: (k1_relat_1(B_120)=A_121 | ~v1_partfun1(B_120, A_121) | ~v4_relat_1(B_120, A_121) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.19/1.47  tff(c_86, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_80])).
% 3.19/1.47  tff(c_92, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_86])).
% 3.19/1.47  tff(c_102, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_92])).
% 3.19/1.47  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.19/1.47  tff(c_166, plain, (![C_135, A_136, B_137]: (v1_partfun1(C_135, A_136) | ~v1_funct_2(C_135, A_136, B_137) | ~v1_funct_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | v1_xboole_0(B_137))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.19/1.47  tff(c_173, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_166])).
% 3.19/1.47  tff(c_180, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_173])).
% 3.19/1.47  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_102, c_180])).
% 3.19/1.47  tff(c_183, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_92])).
% 3.19/1.47  tff(c_223, plain, (![C_144, B_145, A_146]: (m1_subset_1(k1_funct_1(C_144, B_145), A_146) | ~r2_hidden(B_145, k1_relat_1(C_144)) | ~v1_funct_1(C_144) | ~v5_relat_1(C_144, A_146) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.47  tff(c_225, plain, (![B_145, A_146]: (m1_subset_1(k1_funct_1('#skF_4', B_145), A_146) | ~r2_hidden(B_145, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_146) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_223])).
% 3.19/1.47  tff(c_232, plain, (![B_145, A_146]: (m1_subset_1(k1_funct_1('#skF_4', B_145), A_146) | ~r2_hidden(B_145, '#skF_2') | ~v5_relat_1('#skF_4', A_146))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_46, c_225])).
% 3.19/1.47  tff(c_399, plain, (![A_179, B_180, C_181, D_182]: (k3_funct_2(A_179, B_180, C_181, D_182)=k7_partfun1(B_180, C_181, D_182) | ~m1_subset_1(D_182, A_179) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_2(C_181, A_179, B_180) | ~v1_funct_1(C_181) | v1_xboole_0(B_180) | v1_xboole_0(A_179))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.19/1.47  tff(c_585, plain, (![A_219, B_220, C_221, B_222]: (k3_funct_2(A_219, B_220, C_221, k1_funct_1('#skF_4', B_222))=k7_partfun1(B_220, C_221, k1_funct_1('#skF_4', B_222)) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~v1_funct_2(C_221, A_219, B_220) | ~v1_funct_1(C_221) | v1_xboole_0(B_220) | v1_xboole_0(A_219) | ~r2_hidden(B_222, '#skF_2') | ~v5_relat_1('#skF_4', A_219))), inference(resolution, [status(thm)], [c_232, c_399])).
% 3.19/1.47  tff(c_598, plain, (![B_222]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_222))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_222)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1') | ~r2_hidden(B_222, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_585])).
% 3.19/1.47  tff(c_608, plain, (![B_222]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_222))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_222)) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1') | ~r2_hidden(B_222, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_40, c_222, c_598])).
% 3.19/1.47  tff(c_610, plain, (![B_223]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_223))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_223)) | ~r2_hidden(B_223, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_209, c_608])).
% 3.19/1.47  tff(c_317, plain, (![A_158, B_159, C_160, D_161]: (k3_funct_2(A_158, B_159, C_160, D_161)=k1_funct_1(C_160, D_161) | ~m1_subset_1(D_161, A_158) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_2(C_160, A_158, B_159) | ~v1_funct_1(C_160) | v1_xboole_0(A_158))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.19/1.47  tff(c_475, plain, (![A_199, B_200, C_201, B_202]: (k3_funct_2(A_199, B_200, C_201, k1_funct_1('#skF_4', B_202))=k1_funct_1(C_201, k1_funct_1('#skF_4', B_202)) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_2(C_201, A_199, B_200) | ~v1_funct_1(C_201) | v1_xboole_0(A_199) | ~r2_hidden(B_202, '#skF_2') | ~v5_relat_1('#skF_4', A_199))), inference(resolution, [status(thm)], [c_232, c_317])).
% 3.19/1.47  tff(c_488, plain, (![B_202]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_202))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_202)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_1') | ~r2_hidden(B_202, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_475])).
% 3.19/1.47  tff(c_498, plain, (![B_202]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_202))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_202)) | v1_xboole_0('#skF_1') | ~r2_hidden(B_202, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_40, c_222, c_488])).
% 3.19/1.47  tff(c_499, plain, (![B_202]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_202))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_202)) | ~r2_hidden(B_202, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_498])).
% 3.19/1.47  tff(c_626, plain, (![B_224]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_224))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_224)) | ~r2_hidden(B_224, '#skF_2') | ~r2_hidden(B_224, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_610, c_499])).
% 3.19/1.47  tff(c_327, plain, (![B_159, C_160]: (k3_funct_2('#skF_2', B_159, C_160, '#skF_6')=k1_funct_1(C_160, '#skF_6') | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_159))) | ~v1_funct_2(C_160, '#skF_2', B_159) | ~v1_funct_1(C_160) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_317])).
% 3.19/1.47  tff(c_369, plain, (![B_165, C_166]: (k3_funct_2('#skF_2', B_165, C_166, '#skF_6')=k1_funct_1(C_166, '#skF_6') | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_165))) | ~v1_funct_2(C_166, '#skF_2', B_165) | ~v1_funct_1(C_166))), inference(negUnitSimplification, [status(thm)], [c_48, c_327])).
% 3.19/1.47  tff(c_384, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_369])).
% 3.19/1.47  tff(c_390, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_384])).
% 3.19/1.47  tff(c_449, plain, (![C_193, F_189, B_190, A_192, E_194, D_191]: (k3_funct_2(B_190, C_193, k8_funct_2(B_190, A_192, C_193, D_191, E_194), F_189)=k1_funct_1(E_194, k3_funct_2(B_190, A_192, D_191, F_189)) | ~v1_partfun1(E_194, A_192) | ~m1_subset_1(F_189, B_190) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_192, C_193))) | ~v1_funct_1(E_194) | ~m1_subset_1(D_191, k1_zfmisc_1(k2_zfmisc_1(B_190, A_192))) | ~v1_funct_2(D_191, B_190, A_192) | ~v1_funct_1(D_191) | v1_xboole_0(B_190) | v1_xboole_0(A_192))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.19/1.47  tff(c_462, plain, (![B_190, D_191, F_189]: (k3_funct_2(B_190, '#skF_3', k8_funct_2(B_190, '#skF_1', '#skF_3', D_191, '#skF_5'), F_189)=k1_funct_1('#skF_5', k3_funct_2(B_190, '#skF_1', D_191, F_189)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_189, B_190) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_191, k1_zfmisc_1(k2_zfmisc_1(B_190, '#skF_1'))) | ~v1_funct_2(D_191, B_190, '#skF_1') | ~v1_funct_1(D_191) | v1_xboole_0(B_190) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_449])).
% 3.19/1.47  tff(c_472, plain, (![B_190, D_191, F_189]: (k3_funct_2(B_190, '#skF_3', k8_funct_2(B_190, '#skF_1', '#skF_3', D_191, '#skF_5'), F_189)=k1_funct_1('#skF_5', k3_funct_2(B_190, '#skF_1', D_191, F_189)) | ~m1_subset_1(F_189, B_190) | ~m1_subset_1(D_191, k1_zfmisc_1(k2_zfmisc_1(B_190, '#skF_1'))) | ~v1_funct_2(D_191, B_190, '#skF_1') | ~v1_funct_1(D_191) | v1_xboole_0(B_190) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_462])).
% 3.19/1.47  tff(c_538, plain, (![B_208, D_209, F_210]: (k3_funct_2(B_208, '#skF_3', k8_funct_2(B_208, '#skF_1', '#skF_3', D_209, '#skF_5'), F_210)=k1_funct_1('#skF_5', k3_funct_2(B_208, '#skF_1', D_209, F_210)) | ~m1_subset_1(F_210, B_208) | ~m1_subset_1(D_209, k1_zfmisc_1(k2_zfmisc_1(B_208, '#skF_1'))) | ~v1_funct_2(D_209, B_208, '#skF_1') | ~v1_funct_1(D_209) | v1_xboole_0(B_208))), inference(negUnitSimplification, [status(thm)], [c_50, c_472])).
% 3.19/1.47  tff(c_549, plain, (![F_210]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_210)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_210)) | ~m1_subset_1(F_210, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_538])).
% 3.19/1.47  tff(c_555, plain, (![F_210]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_210)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_210)) | ~m1_subset_1(F_210, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_549])).
% 3.19/1.47  tff(c_557, plain, (![F_211]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_211)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_211)) | ~m1_subset_1(F_211, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_555])).
% 3.19/1.47  tff(c_32, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.19/1.47  tff(c_391, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_390, c_32])).
% 3.19/1.47  tff(c_563, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_557, c_391])).
% 3.19/1.47  tff(c_569, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_390, c_563])).
% 3.19/1.47  tff(c_637, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_626, c_569])).
% 3.19/1.47  tff(c_641, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_637])).
% 3.19/1.47  tff(c_644, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_641])).
% 3.19/1.47  tff(c_646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_644])).
% 3.19/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.47  
% 3.19/1.47  Inference rules
% 3.19/1.47  ----------------------
% 3.19/1.47  #Ref     : 0
% 3.19/1.47  #Sup     : 119
% 3.19/1.47  #Fact    : 0
% 3.19/1.47  #Define  : 0
% 3.19/1.47  #Split   : 9
% 3.19/1.47  #Chain   : 0
% 3.19/1.47  #Close   : 0
% 3.19/1.47  
% 3.19/1.47  Ordering : KBO
% 3.19/1.47  
% 3.19/1.47  Simplification rules
% 3.19/1.47  ----------------------
% 3.19/1.47  #Subsume      : 33
% 3.19/1.47  #Demod        : 67
% 3.19/1.47  #Tautology    : 24
% 3.19/1.47  #SimpNegUnit  : 20
% 3.19/1.47  #BackRed      : 1
% 3.19/1.47  
% 3.19/1.47  #Partial instantiations: 0
% 3.19/1.47  #Strategies tried      : 1
% 3.19/1.47  
% 3.19/1.47  Timing (in seconds)
% 3.19/1.47  ----------------------
% 3.26/1.48  Preprocessing        : 0.36
% 3.26/1.48  Parsing              : 0.19
% 3.26/1.48  CNF conversion       : 0.03
% 3.26/1.48  Main loop            : 0.35
% 3.26/1.48  Inferencing          : 0.13
% 3.26/1.48  Reduction            : 0.11
% 3.26/1.48  Demodulation         : 0.07
% 3.26/1.48  BG Simplification    : 0.02
% 3.26/1.48  Subsumption          : 0.06
% 3.26/1.48  Abstraction          : 0.02
% 3.26/1.48  MUC search           : 0.00
% 3.26/1.48  Cooper               : 0.00
% 3.26/1.48  Total                : 0.75
% 3.26/1.48  Index Insertion      : 0.00
% 3.26/1.48  Index Deletion       : 0.00
% 3.26/1.48  Index Matching       : 0.00
% 3.26/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
