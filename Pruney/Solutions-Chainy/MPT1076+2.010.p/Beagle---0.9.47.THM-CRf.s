%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:13 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 294 expanded)
%              Number of leaves         :   38 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  245 (1177 expanded)
%              Number of equality atoms :   51 ( 174 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_148,axiom,(
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

tff(f_30,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_122,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_40,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_218,plain,(
    ! [C_141,A_142,B_143] :
      ( ~ v1_partfun1(C_141,A_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_xboole_0(B_143)
      | v1_xboole_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_224,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_218])).

tff(c_231,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_224])).

tff(c_232,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_231])).

tff(c_42,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_281,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k3_funct_2(A_162,B_163,C_164,D_165) = k1_funct_1(C_164,D_165)
      | ~ m1_subset_1(D_165,A_162)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_2(C_164,A_162,B_163)
      | ~ v1_funct_1(C_164)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_291,plain,(
    ! [B_163,C_164] :
      ( k3_funct_2('#skF_2',B_163,C_164,'#skF_6') = k1_funct_1(C_164,'#skF_6')
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_163)))
      | ~ v1_funct_2(C_164,'#skF_2',B_163)
      | ~ v1_funct_1(C_164)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_281])).

tff(c_303,plain,(
    ! [B_166,C_167] :
      ( k3_funct_2('#skF_2',B_166,C_167,'#skF_6') = k1_funct_1(C_167,'#skF_6')
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_166)))
      | ~ v1_funct_2(C_167,'#skF_2',B_166)
      | ~ v1_funct_1(C_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_291])).

tff(c_306,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_303])).

tff(c_309,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_306])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_427,plain,(
    ! [F_184,B_185,A_187,C_188,E_186,D_189] :
      ( k3_funct_2(B_185,C_188,k8_funct_2(B_185,A_187,C_188,D_189,E_186),F_184) = k1_funct_1(E_186,k3_funct_2(B_185,A_187,D_189,F_184))
      | ~ v1_partfun1(E_186,A_187)
      | ~ m1_subset_1(F_184,B_185)
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1(A_187,C_188)))
      | ~ v1_funct_1(E_186)
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(B_185,A_187)))
      | ~ v1_funct_2(D_189,B_185,A_187)
      | ~ v1_funct_1(D_189)
      | v1_xboole_0(B_185)
      | v1_xboole_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_431,plain,(
    ! [B_185,D_189,F_184] :
      ( k3_funct_2(B_185,'#skF_3',k8_funct_2(B_185,'#skF_1','#skF_3',D_189,'#skF_5'),F_184) = k1_funct_1('#skF_5',k3_funct_2(B_185,'#skF_1',D_189,F_184))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_184,B_185)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(B_185,'#skF_1')))
      | ~ v1_funct_2(D_189,B_185,'#skF_1')
      | ~ v1_funct_1(D_189)
      | v1_xboole_0(B_185)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_427])).

tff(c_438,plain,(
    ! [B_185,D_189,F_184] :
      ( k3_funct_2(B_185,'#skF_3',k8_funct_2(B_185,'#skF_1','#skF_3',D_189,'#skF_5'),F_184) = k1_funct_1('#skF_5',k3_funct_2(B_185,'#skF_1',D_189,F_184))
      | ~ m1_subset_1(F_184,B_185)
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(B_185,'#skF_1')))
      | ~ v1_funct_2(D_189,B_185,'#skF_1')
      | ~ v1_funct_1(D_189)
      | v1_xboole_0(B_185)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_431])).

tff(c_458,plain,(
    ! [B_196,D_197,F_198] :
      ( k3_funct_2(B_196,'#skF_3',k8_funct_2(B_196,'#skF_1','#skF_3',D_197,'#skF_5'),F_198) = k1_funct_1('#skF_5',k3_funct_2(B_196,'#skF_1',D_197,F_198))
      | ~ m1_subset_1(F_198,B_196)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(B_196,'#skF_1')))
      | ~ v1_funct_2(D_197,B_196,'#skF_1')
      | ~ v1_funct_1(D_197)
      | v1_xboole_0(B_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_438])).

tff(c_460,plain,(
    ! [F_198] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_198) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_198))
      | ~ m1_subset_1(F_198,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_458])).

tff(c_463,plain,(
    ! [F_198] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_198) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_198))
      | ~ m1_subset_1(F_198,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_460])).

tff(c_465,plain,(
    ! [F_199] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_199) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_199))
      | ~ m1_subset_1(F_199,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_463])).

tff(c_57,plain,(
    ! [C_106,A_107,B_108] :
      ( v1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_65,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_57])).

tff(c_66,plain,(
    ! [C_109,A_110,B_111] :
      ( v4_relat_1(C_109,A_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_85,plain,(
    ! [B_116,A_117] :
      ( k1_relat_1(B_116) = A_117
      | ~ v1_partfun1(B_116,A_117)
      | ~ v4_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_88,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_85])).

tff(c_94,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_40,c_88])).

tff(c_203,plain,(
    ! [A_138,B_139,C_140] :
      ( k1_relset_1(A_138,B_139,C_140) = k1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_209,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_203])).

tff(c_213,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_209])).

tff(c_252,plain,(
    ! [B_153,C_154,A_155] :
      ( k1_xboole_0 = B_153
      | v1_funct_2(C_154,A_155,B_153)
      | k1_relset_1(A_155,B_153,C_154) != A_155
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_258,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_5','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_5') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_252])).

tff(c_264,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_258])).

tff(c_265,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_266,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( m1_subset_1(k3_funct_2(A_156,B_157,C_158,D_159),B_157)
      | ~ m1_subset_1(D_159,A_156)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_2(C_158,A_156,B_157)
      | ~ v1_funct_1(C_158)
      | v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_268,plain,(
    ! [D_159] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_159),'#skF_1')
      | ~ m1_subset_1(D_159,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_266])).

tff(c_273,plain,(
    ! [D_159] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_159),'#skF_1')
      | ~ m1_subset_1(D_159,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_268])).

tff(c_274,plain,(
    ! [D_159] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_159),'#skF_1')
      | ~ m1_subset_1(D_159,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_273])).

tff(c_314,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_274])).

tff(c_318,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_314])).

tff(c_32,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k3_funct_2(A_23,B_24,C_25,D_26) = k1_funct_1(C_25,D_26)
      | ~ m1_subset_1(D_26,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_321,plain,(
    ! [B_24,C_25] :
      ( k3_funct_2('#skF_1',B_24,C_25,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_25,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_24)))
      | ~ v1_funct_2(C_25,'#skF_1',B_24)
      | ~ v1_funct_1(C_25)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_318,c_32])).

tff(c_325,plain,(
    ! [B_168,C_169] :
      ( k3_funct_2('#skF_1',B_168,C_169,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_169,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_168)))
      | ~ v1_funct_2(C_169,'#skF_1',B_168)
      | ~ v1_funct_1(C_169) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_321])).

tff(c_328,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_325])).

tff(c_331,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_265,c_328])).

tff(c_341,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k3_funct_2(A_170,B_171,C_172,D_173) = k7_partfun1(B_171,C_172,D_173)
      | ~ m1_subset_1(D_173,A_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_2(C_172,A_170,B_171)
      | ~ v1_funct_1(C_172)
      | v1_xboole_0(B_171)
      | v1_xboole_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_343,plain,(
    ! [B_171,C_172] :
      ( k3_funct_2('#skF_1',B_171,C_172,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_171,C_172,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_171)))
      | ~ v1_funct_2(C_172,'#skF_1',B_171)
      | ~ v1_funct_1(C_172)
      | v1_xboole_0(B_171)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_318,c_341])).

tff(c_390,plain,(
    ! [B_176,C_177] :
      ( k3_funct_2('#skF_1',B_176,C_177,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_176,C_177,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_176)))
      | ~ v1_funct_2(C_177,'#skF_1',B_176)
      | ~ v1_funct_1(C_177)
      | v1_xboole_0(B_176) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_343])).

tff(c_393,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_390])).

tff(c_396,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_265,c_331,c_393])).

tff(c_397,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_396])).

tff(c_38,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_310,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_38])).

tff(c_398,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_310])).

tff(c_471,plain,
    ( k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_398])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_309,c_471])).

tff(c_479,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_487,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_2])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:58:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.87/1.44  
% 2.87/1.44  %Foreground sorts:
% 2.87/1.44  
% 2.87/1.44  
% 2.87/1.44  %Background operators:
% 2.87/1.44  
% 2.87/1.44  
% 2.87/1.44  %Foreground operators:
% 2.87/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.44  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.87/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.44  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.87/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.87/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.87/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.44  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.87/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.44  
% 2.87/1.46  tff(f_175, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 2.87/1.46  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 2.87/1.46  tff(f_103, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.87/1.46  tff(f_148, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 2.87/1.46  tff(f_30, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.87/1.46  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.87/1.46  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.87/1.46  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.87/1.46  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.87/1.46  tff(f_90, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.87/1.46  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 2.87/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.87/1.46  tff(c_56, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.87/1.46  tff(c_40, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.87/1.46  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.87/1.46  tff(c_218, plain, (![C_141, A_142, B_143]: (~v1_partfun1(C_141, A_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_xboole_0(B_143) | v1_xboole_0(A_142))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.87/1.46  tff(c_224, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_218])).
% 2.87/1.46  tff(c_231, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_224])).
% 2.87/1.46  tff(c_232, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_231])).
% 2.87/1.46  tff(c_42, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.87/1.46  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.87/1.46  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.87/1.46  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.87/1.46  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.87/1.46  tff(c_281, plain, (![A_162, B_163, C_164, D_165]: (k3_funct_2(A_162, B_163, C_164, D_165)=k1_funct_1(C_164, D_165) | ~m1_subset_1(D_165, A_162) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_2(C_164, A_162, B_163) | ~v1_funct_1(C_164) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.87/1.46  tff(c_291, plain, (![B_163, C_164]: (k3_funct_2('#skF_2', B_163, C_164, '#skF_6')=k1_funct_1(C_164, '#skF_6') | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_163))) | ~v1_funct_2(C_164, '#skF_2', B_163) | ~v1_funct_1(C_164) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_281])).
% 2.87/1.46  tff(c_303, plain, (![B_166, C_167]: (k3_funct_2('#skF_2', B_166, C_167, '#skF_6')=k1_funct_1(C_167, '#skF_6') | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_166))) | ~v1_funct_2(C_167, '#skF_2', B_166) | ~v1_funct_1(C_167))), inference(negUnitSimplification, [status(thm)], [c_54, c_291])).
% 2.87/1.46  tff(c_306, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_303])).
% 2.87/1.46  tff(c_309, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_306])).
% 2.87/1.46  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.87/1.46  tff(c_427, plain, (![F_184, B_185, A_187, C_188, E_186, D_189]: (k3_funct_2(B_185, C_188, k8_funct_2(B_185, A_187, C_188, D_189, E_186), F_184)=k1_funct_1(E_186, k3_funct_2(B_185, A_187, D_189, F_184)) | ~v1_partfun1(E_186, A_187) | ~m1_subset_1(F_184, B_185) | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1(A_187, C_188))) | ~v1_funct_1(E_186) | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(B_185, A_187))) | ~v1_funct_2(D_189, B_185, A_187) | ~v1_funct_1(D_189) | v1_xboole_0(B_185) | v1_xboole_0(A_187))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.87/1.46  tff(c_431, plain, (![B_185, D_189, F_184]: (k3_funct_2(B_185, '#skF_3', k8_funct_2(B_185, '#skF_1', '#skF_3', D_189, '#skF_5'), F_184)=k1_funct_1('#skF_5', k3_funct_2(B_185, '#skF_1', D_189, F_184)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_184, B_185) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(B_185, '#skF_1'))) | ~v1_funct_2(D_189, B_185, '#skF_1') | ~v1_funct_1(D_189) | v1_xboole_0(B_185) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_427])).
% 2.87/1.46  tff(c_438, plain, (![B_185, D_189, F_184]: (k3_funct_2(B_185, '#skF_3', k8_funct_2(B_185, '#skF_1', '#skF_3', D_189, '#skF_5'), F_184)=k1_funct_1('#skF_5', k3_funct_2(B_185, '#skF_1', D_189, F_184)) | ~m1_subset_1(F_184, B_185) | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(B_185, '#skF_1'))) | ~v1_funct_2(D_189, B_185, '#skF_1') | ~v1_funct_1(D_189) | v1_xboole_0(B_185) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_431])).
% 2.87/1.46  tff(c_458, plain, (![B_196, D_197, F_198]: (k3_funct_2(B_196, '#skF_3', k8_funct_2(B_196, '#skF_1', '#skF_3', D_197, '#skF_5'), F_198)=k1_funct_1('#skF_5', k3_funct_2(B_196, '#skF_1', D_197, F_198)) | ~m1_subset_1(F_198, B_196) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(B_196, '#skF_1'))) | ~v1_funct_2(D_197, B_196, '#skF_1') | ~v1_funct_1(D_197) | v1_xboole_0(B_196))), inference(negUnitSimplification, [status(thm)], [c_56, c_438])).
% 2.87/1.46  tff(c_460, plain, (![F_198]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_198)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_198)) | ~m1_subset_1(F_198, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_458])).
% 2.87/1.46  tff(c_463, plain, (![F_198]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_198)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_198)) | ~m1_subset_1(F_198, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_460])).
% 2.87/1.46  tff(c_465, plain, (![F_199]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_199)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_199)) | ~m1_subset_1(F_199, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_463])).
% 2.87/1.46  tff(c_57, plain, (![C_106, A_107, B_108]: (v1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.87/1.46  tff(c_65, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_57])).
% 2.87/1.46  tff(c_66, plain, (![C_109, A_110, B_111]: (v4_relat_1(C_109, A_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.87/1.46  tff(c_74, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_66])).
% 2.87/1.46  tff(c_85, plain, (![B_116, A_117]: (k1_relat_1(B_116)=A_117 | ~v1_partfun1(B_116, A_117) | ~v4_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.46  tff(c_88, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_85])).
% 2.87/1.46  tff(c_94, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_40, c_88])).
% 2.87/1.46  tff(c_203, plain, (![A_138, B_139, C_140]: (k1_relset_1(A_138, B_139, C_140)=k1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.46  tff(c_209, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_203])).
% 2.87/1.46  tff(c_213, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_209])).
% 2.87/1.46  tff(c_252, plain, (![B_153, C_154, A_155]: (k1_xboole_0=B_153 | v1_funct_2(C_154, A_155, B_153) | k1_relset_1(A_155, B_153, C_154)!=A_155 | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_153))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.87/1.46  tff(c_258, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_5', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_5')!='#skF_1'), inference(resolution, [status(thm)], [c_44, c_252])).
% 2.87/1.46  tff(c_264, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_258])).
% 2.87/1.46  tff(c_265, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_264])).
% 2.87/1.46  tff(c_266, plain, (![A_156, B_157, C_158, D_159]: (m1_subset_1(k3_funct_2(A_156, B_157, C_158, D_159), B_157) | ~m1_subset_1(D_159, A_156) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_2(C_158, A_156, B_157) | ~v1_funct_1(C_158) | v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.87/1.46  tff(c_268, plain, (![D_159]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_159), '#skF_1') | ~m1_subset_1(D_159, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_266])).
% 2.87/1.46  tff(c_273, plain, (![D_159]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_159), '#skF_1') | ~m1_subset_1(D_159, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_268])).
% 2.87/1.46  tff(c_274, plain, (![D_159]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_159), '#skF_1') | ~m1_subset_1(D_159, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_273])).
% 2.87/1.46  tff(c_314, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_309, c_274])).
% 2.87/1.46  tff(c_318, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_314])).
% 2.87/1.46  tff(c_32, plain, (![A_23, B_24, C_25, D_26]: (k3_funct_2(A_23, B_24, C_25, D_26)=k1_funct_1(C_25, D_26) | ~m1_subset_1(D_26, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.87/1.46  tff(c_321, plain, (![B_24, C_25]: (k3_funct_2('#skF_1', B_24, C_25, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_25, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_24))) | ~v1_funct_2(C_25, '#skF_1', B_24) | ~v1_funct_1(C_25) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_318, c_32])).
% 2.87/1.46  tff(c_325, plain, (![B_168, C_169]: (k3_funct_2('#skF_1', B_168, C_169, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_169, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_168))) | ~v1_funct_2(C_169, '#skF_1', B_168) | ~v1_funct_1(C_169))), inference(negUnitSimplification, [status(thm)], [c_56, c_321])).
% 2.87/1.46  tff(c_328, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_325])).
% 2.87/1.46  tff(c_331, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_265, c_328])).
% 2.87/1.46  tff(c_341, plain, (![A_170, B_171, C_172, D_173]: (k3_funct_2(A_170, B_171, C_172, D_173)=k7_partfun1(B_171, C_172, D_173) | ~m1_subset_1(D_173, A_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~v1_funct_2(C_172, A_170, B_171) | ~v1_funct_1(C_172) | v1_xboole_0(B_171) | v1_xboole_0(A_170))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.87/1.46  tff(c_343, plain, (![B_171, C_172]: (k3_funct_2('#skF_1', B_171, C_172, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_171, C_172, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_171))) | ~v1_funct_2(C_172, '#skF_1', B_171) | ~v1_funct_1(C_172) | v1_xboole_0(B_171) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_318, c_341])).
% 2.87/1.46  tff(c_390, plain, (![B_176, C_177]: (k3_funct_2('#skF_1', B_176, C_177, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_176, C_177, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_176))) | ~v1_funct_2(C_177, '#skF_1', B_176) | ~v1_funct_1(C_177) | v1_xboole_0(B_176))), inference(negUnitSimplification, [status(thm)], [c_56, c_343])).
% 2.87/1.46  tff(c_393, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_390])).
% 2.87/1.46  tff(c_396, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_265, c_331, c_393])).
% 2.87/1.46  tff(c_397, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_232, c_396])).
% 2.87/1.46  tff(c_38, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.87/1.46  tff(c_310, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_38])).
% 2.87/1.46  tff(c_398, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_310])).
% 2.87/1.46  tff(c_471, plain, (k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_465, c_398])).
% 2.87/1.46  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_309, c_471])).
% 2.87/1.46  tff(c_479, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_264])).
% 2.87/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.87/1.46  tff(c_487, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_2])).
% 2.87/1.46  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_487])).
% 2.87/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  Inference rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Ref     : 0
% 2.87/1.46  #Sup     : 85
% 2.87/1.46  #Fact    : 0
% 2.87/1.46  #Define  : 0
% 2.87/1.46  #Split   : 3
% 2.87/1.46  #Chain   : 0
% 2.87/1.46  #Close   : 0
% 2.87/1.46  
% 2.87/1.46  Ordering : KBO
% 2.87/1.46  
% 2.87/1.46  Simplification rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Subsume      : 2
% 2.87/1.46  #Demod        : 108
% 2.87/1.46  #Tautology    : 33
% 2.87/1.46  #SimpNegUnit  : 26
% 2.87/1.46  #BackRed      : 17
% 2.87/1.46  
% 2.87/1.46  #Partial instantiations: 0
% 2.87/1.46  #Strategies tried      : 1
% 2.87/1.46  
% 2.87/1.46  Timing (in seconds)
% 2.87/1.46  ----------------------
% 2.87/1.46  Preprocessing        : 0.34
% 2.87/1.46  Parsing              : 0.17
% 2.87/1.46  CNF conversion       : 0.03
% 2.87/1.46  Main loop            : 0.29
% 2.87/1.46  Inferencing          : 0.10
% 3.05/1.46  Reduction            : 0.09
% 3.05/1.47  Demodulation         : 0.07
% 3.05/1.47  BG Simplification    : 0.02
% 3.05/1.47  Subsumption          : 0.05
% 3.05/1.47  Abstraction          : 0.01
% 3.05/1.47  MUC search           : 0.00
% 3.05/1.47  Cooper               : 0.00
% 3.05/1.47  Total                : 0.67
% 3.05/1.47  Index Insertion      : 0.00
% 3.05/1.47  Index Deletion       : 0.00
% 3.05/1.47  Index Matching       : 0.00
% 3.05/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
