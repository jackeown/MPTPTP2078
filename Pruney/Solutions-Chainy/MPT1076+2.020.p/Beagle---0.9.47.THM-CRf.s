%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:15 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 280 expanded)
%              Number of leaves         :   38 ( 115 expanded)
%              Depth                    :   16
%              Number of atoms          :  267 (1154 expanded)
%              Number of equality atoms :   35 ( 118 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_136,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_110,axiom,(
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

tff(c_38,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_260,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k3_funct_2(A_146,B_147,C_148,D_149) = k1_funct_1(C_148,D_149)
      | ~ m1_subset_1(D_149,A_146)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ v1_funct_2(C_148,A_146,B_147)
      | ~ v1_funct_1(C_148)
      | v1_xboole_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_274,plain,(
    ! [B_147,C_148] :
      ( k3_funct_2('#skF_2',B_147,C_148,'#skF_6') = k1_funct_1(C_148,'#skF_6')
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_147)))
      | ~ v1_funct_2(C_148,'#skF_2',B_147)
      | ~ v1_funct_1(C_148)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_260])).

tff(c_361,plain,(
    ! [B_158,C_159] :
      ( k3_funct_2('#skF_2',B_158,C_159,'#skF_6') = k1_funct_1(C_159,'#skF_6')
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_158)))
      | ~ v1_funct_2(C_159,'#skF_2',B_158)
      | ~ v1_funct_1(C_159) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_274])).

tff(c_368,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_361])).

tff(c_372,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_368])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_36,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_484,plain,(
    ! [D_173,E_174,A_171,F_172,C_175,B_170] :
      ( k3_funct_2(B_170,C_175,k8_funct_2(B_170,A_171,C_175,D_173,E_174),F_172) = k1_funct_1(E_174,k3_funct_2(B_170,A_171,D_173,F_172))
      | ~ v1_partfun1(E_174,A_171)
      | ~ m1_subset_1(F_172,B_170)
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(A_171,C_175)))
      | ~ v1_funct_1(E_174)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(B_170,A_171)))
      | ~ v1_funct_2(D_173,B_170,A_171)
      | ~ v1_funct_1(D_173)
      | v1_xboole_0(B_170)
      | v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_495,plain,(
    ! [B_170,D_173,F_172] :
      ( k3_funct_2(B_170,'#skF_3',k8_funct_2(B_170,'#skF_1','#skF_3',D_173,'#skF_5'),F_172) = k1_funct_1('#skF_5',k3_funct_2(B_170,'#skF_1',D_173,F_172))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_172,B_170)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(B_170,'#skF_1')))
      | ~ v1_funct_2(D_173,B_170,'#skF_1')
      | ~ v1_funct_1(D_173)
      | v1_xboole_0(B_170)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_484])).

tff(c_508,plain,(
    ! [B_170,D_173,F_172] :
      ( k3_funct_2(B_170,'#skF_3',k8_funct_2(B_170,'#skF_1','#skF_3',D_173,'#skF_5'),F_172) = k1_funct_1('#skF_5',k3_funct_2(B_170,'#skF_1',D_173,F_172))
      | ~ m1_subset_1(F_172,B_170)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(B_170,'#skF_1')))
      | ~ v1_funct_2(D_173,B_170,'#skF_1')
      | ~ v1_funct_1(D_173)
      | v1_xboole_0(B_170)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_495])).

tff(c_897,plain,(
    ! [B_206,D_207,F_208] :
      ( k3_funct_2(B_206,'#skF_3',k8_funct_2(B_206,'#skF_1','#skF_3',D_207,'#skF_5'),F_208) = k1_funct_1('#skF_5',k3_funct_2(B_206,'#skF_1',D_207,F_208))
      | ~ m1_subset_1(F_208,B_206)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(B_206,'#skF_1')))
      | ~ v1_funct_2(D_207,B_206,'#skF_1')
      | ~ v1_funct_1(D_207)
      | v1_xboole_0(B_206) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_508])).

tff(c_917,plain,(
    ! [F_208] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_208) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_208))
      | ~ m1_subset_1(F_208,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_897])).

tff(c_929,plain,(
    ! [F_208] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_208) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_208))
      | ~ m1_subset_1(F_208,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_917])).

tff(c_931,plain,(
    ! [F_209] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_209) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_209))
      | ~ m1_subset_1(F_209,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_929])).

tff(c_114,plain,(
    ! [C_123,A_124,B_125] :
      ( ~ v1_partfun1(C_123,A_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_xboole_0(B_125)
      | v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_120,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_114])).

tff(c_125,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_120])).

tff(c_126,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_125])).

tff(c_68,plain,(
    ! [C_112,B_113,A_114] :
      ( v5_relat_1(C_112,B_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    ! [B_108,A_109] :
      ( v1_relat_1(B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_109))
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_54])).

tff(c_66,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_60])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    ! [C_115,A_116,B_117] :
      ( v4_relat_1(C_115,A_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_85,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_77])).

tff(c_92,plain,(
    ! [B_121,A_122] :
      ( k1_relat_1(B_121) = A_122
      | ~ v1_partfun1(B_121,A_122)
      | ~ v4_relat_1(B_121,A_122)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_98,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_85,c_92])).

tff(c_104,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36,c_98])).

tff(c_128,plain,(
    ! [B_126,A_127] :
      ( v1_funct_2(B_126,k1_relat_1(B_126),A_127)
      | ~ r1_tarski(k2_relat_1(B_126),A_127)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_131,plain,(
    ! [A_127] :
      ( v1_funct_2('#skF_5','#skF_1',A_127)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_127)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_128])).

tff(c_134,plain,(
    ! [A_128] :
      ( v1_funct_2('#skF_5','#skF_1',A_128)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_42,c_131])).

tff(c_138,plain,(
    ! [A_4] :
      ( v1_funct_2('#skF_5','#skF_1',A_4)
      | ~ v5_relat_1('#skF_5',A_4)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_141,plain,(
    ! [A_4] :
      ( v1_funct_2('#skF_5','#skF_1',A_4)
      | ~ v5_relat_1('#skF_5',A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_138])).

tff(c_198,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( m1_subset_1(k3_funct_2(A_134,B_135,C_136,D_137),B_135)
      | ~ m1_subset_1(D_137,A_134)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_2(C_136,A_134,B_135)
      | ~ v1_funct_1(C_136)
      | v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_206,plain,(
    ! [D_137] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_3','#skF_5',D_137),'#skF_3')
      | ~ m1_subset_1(D_137,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_198])).

tff(c_218,plain,(
    ! [D_137] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_3','#skF_5',D_137),'#skF_3')
      | ~ m1_subset_1(D_137,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_206])).

tff(c_219,plain,(
    ! [D_137] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_3','#skF_5',D_137),'#skF_3')
      | ~ m1_subset_1(D_137,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_218])).

tff(c_234,plain,(
    ~ v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_237,plain,(
    ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_234])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_237])).

tff(c_243,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_204,plain,(
    ! [D_137] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_137),'#skF_1')
      | ~ m1_subset_1(D_137,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_198])).

tff(c_214,plain,(
    ! [D_137] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_137),'#skF_1')
      | ~ m1_subset_1(D_137,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_204])).

tff(c_215,plain,(
    ! [D_137] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_137),'#skF_1')
      | ~ m1_subset_1(D_137,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_214])).

tff(c_408,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_215])).

tff(c_412,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_408])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23,D_24] :
      ( k3_funct_2(A_21,B_22,C_23,D_24) = k1_funct_1(C_23,D_24)
      | ~ m1_subset_1(D_24,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_417,plain,(
    ! [B_22,C_23] :
      ( k3_funct_2('#skF_1',B_22,C_23,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_23,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_22)))
      | ~ v1_funct_2(C_23,'#skF_1',B_22)
      | ~ v1_funct_1(C_23)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_412,c_22])).

tff(c_442,plain,(
    ! [B_168,C_169] :
      ( k3_funct_2('#skF_1',B_168,C_169,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_169,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_168)))
      | ~ v1_funct_2(C_169,'#skF_1',B_168)
      | ~ v1_funct_1(C_169) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_417])).

tff(c_452,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_442])).

tff(c_459,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_243,c_452])).

tff(c_24,plain,(
    ! [A_25,B_33,C_37,D_39] :
      ( k3_funct_2(A_25,B_33,C_37,D_39) = k7_partfun1(B_33,C_37,D_39)
      | ~ m1_subset_1(D_39,A_25)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_25,B_33)))
      | ~ v1_funct_2(C_37,A_25,B_33)
      | ~ v1_funct_1(C_37)
      | v1_xboole_0(B_33)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_415,plain,(
    ! [B_33,C_37] :
      ( k3_funct_2('#skF_1',B_33,C_37,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_33,C_37,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_33)))
      | ~ v1_funct_2(C_37,'#skF_1',B_33)
      | ~ v1_funct_1(C_37)
      | v1_xboole_0(B_33)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_412,c_24])).

tff(c_557,plain,(
    ! [B_178,C_179] :
      ( k3_funct_2('#skF_1',B_178,C_179,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_178,C_179,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_178)))
      | ~ v1_funct_2(C_179,'#skF_1',B_178)
      | ~ v1_funct_1(C_179)
      | v1_xboole_0(B_178) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_415])).

tff(c_567,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_557])).

tff(c_574,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_243,c_459,c_567])).

tff(c_575,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_574])).

tff(c_34,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_404,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_34])).

tff(c_576,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_404])).

tff(c_937,plain,
    ( k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_576])).

tff(c_944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_372,c_937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:12:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.54  
% 3.55/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.55/1.54  
% 3.55/1.54  %Foreground sorts:
% 3.55/1.54  
% 3.55/1.54  
% 3.55/1.54  %Background operators:
% 3.55/1.54  
% 3.55/1.54  
% 3.55/1.54  %Foreground operators:
% 3.55/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.54  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.55/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.55/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.55/1.54  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.55/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.55/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.54  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.55/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.55/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.55/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.55/1.54  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.55/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.54  
% 3.55/1.56  tff(f_175, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 3.55/1.56  tff(f_91, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.55/1.56  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 3.55/1.56  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 3.55/1.56  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.55/1.56  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.55/1.56  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.55/1.56  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.55/1.56  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.55/1.56  tff(f_148, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.55/1.56  tff(f_78, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 3.55/1.56  tff(f_110, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 3.55/1.56  tff(c_38, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.55/1.56  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.55/1.56  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.55/1.56  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.55/1.56  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.55/1.56  tff(c_260, plain, (![A_146, B_147, C_148, D_149]: (k3_funct_2(A_146, B_147, C_148, D_149)=k1_funct_1(C_148, D_149) | ~m1_subset_1(D_149, A_146) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~v1_funct_2(C_148, A_146, B_147) | ~v1_funct_1(C_148) | v1_xboole_0(A_146))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.55/1.56  tff(c_274, plain, (![B_147, C_148]: (k3_funct_2('#skF_2', B_147, C_148, '#skF_6')=k1_funct_1(C_148, '#skF_6') | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_147))) | ~v1_funct_2(C_148, '#skF_2', B_147) | ~v1_funct_1(C_148) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_260])).
% 3.55/1.56  tff(c_361, plain, (![B_158, C_159]: (k3_funct_2('#skF_2', B_158, C_159, '#skF_6')=k1_funct_1(C_159, '#skF_6') | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_158))) | ~v1_funct_2(C_159, '#skF_2', B_158) | ~v1_funct_1(C_159))), inference(negUnitSimplification, [status(thm)], [c_50, c_274])).
% 3.55/1.56  tff(c_368, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_361])).
% 3.55/1.56  tff(c_372, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_368])).
% 3.55/1.56  tff(c_52, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.55/1.56  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.55/1.56  tff(c_36, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.55/1.56  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.55/1.56  tff(c_484, plain, (![D_173, E_174, A_171, F_172, C_175, B_170]: (k3_funct_2(B_170, C_175, k8_funct_2(B_170, A_171, C_175, D_173, E_174), F_172)=k1_funct_1(E_174, k3_funct_2(B_170, A_171, D_173, F_172)) | ~v1_partfun1(E_174, A_171) | ~m1_subset_1(F_172, B_170) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(A_171, C_175))) | ~v1_funct_1(E_174) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(B_170, A_171))) | ~v1_funct_2(D_173, B_170, A_171) | ~v1_funct_1(D_173) | v1_xboole_0(B_170) | v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.55/1.56  tff(c_495, plain, (![B_170, D_173, F_172]: (k3_funct_2(B_170, '#skF_3', k8_funct_2(B_170, '#skF_1', '#skF_3', D_173, '#skF_5'), F_172)=k1_funct_1('#skF_5', k3_funct_2(B_170, '#skF_1', D_173, F_172)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_172, B_170) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(B_170, '#skF_1'))) | ~v1_funct_2(D_173, B_170, '#skF_1') | ~v1_funct_1(D_173) | v1_xboole_0(B_170) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_484])).
% 3.55/1.56  tff(c_508, plain, (![B_170, D_173, F_172]: (k3_funct_2(B_170, '#skF_3', k8_funct_2(B_170, '#skF_1', '#skF_3', D_173, '#skF_5'), F_172)=k1_funct_1('#skF_5', k3_funct_2(B_170, '#skF_1', D_173, F_172)) | ~m1_subset_1(F_172, B_170) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(B_170, '#skF_1'))) | ~v1_funct_2(D_173, B_170, '#skF_1') | ~v1_funct_1(D_173) | v1_xboole_0(B_170) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_495])).
% 3.55/1.56  tff(c_897, plain, (![B_206, D_207, F_208]: (k3_funct_2(B_206, '#skF_3', k8_funct_2(B_206, '#skF_1', '#skF_3', D_207, '#skF_5'), F_208)=k1_funct_1('#skF_5', k3_funct_2(B_206, '#skF_1', D_207, F_208)) | ~m1_subset_1(F_208, B_206) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(B_206, '#skF_1'))) | ~v1_funct_2(D_207, B_206, '#skF_1') | ~v1_funct_1(D_207) | v1_xboole_0(B_206))), inference(negUnitSimplification, [status(thm)], [c_52, c_508])).
% 3.55/1.56  tff(c_917, plain, (![F_208]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_208)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_208)) | ~m1_subset_1(F_208, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_897])).
% 3.55/1.56  tff(c_929, plain, (![F_208]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_208)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_208)) | ~m1_subset_1(F_208, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_917])).
% 3.55/1.56  tff(c_931, plain, (![F_209]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_209)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_209)) | ~m1_subset_1(F_209, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_929])).
% 3.55/1.56  tff(c_114, plain, (![C_123, A_124, B_125]: (~v1_partfun1(C_123, A_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_xboole_0(B_125) | v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.55/1.56  tff(c_120, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_114])).
% 3.55/1.56  tff(c_125, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_120])).
% 3.55/1.56  tff(c_126, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_125])).
% 3.55/1.56  tff(c_68, plain, (![C_112, B_113, A_114]: (v5_relat_1(C_112, B_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.56  tff(c_76, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_68])).
% 3.55/1.56  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.56  tff(c_54, plain, (![B_108, A_109]: (v1_relat_1(B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(A_109)) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.56  tff(c_60, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_54])).
% 3.55/1.56  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_60])).
% 3.55/1.56  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.55/1.56  tff(c_77, plain, (![C_115, A_116, B_117]: (v4_relat_1(C_115, A_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.56  tff(c_85, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_77])).
% 3.55/1.56  tff(c_92, plain, (![B_121, A_122]: (k1_relat_1(B_121)=A_122 | ~v1_partfun1(B_121, A_122) | ~v4_relat_1(B_121, A_122) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.55/1.56  tff(c_98, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_85, c_92])).
% 3.55/1.56  tff(c_104, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_36, c_98])).
% 3.55/1.56  tff(c_128, plain, (![B_126, A_127]: (v1_funct_2(B_126, k1_relat_1(B_126), A_127) | ~r1_tarski(k2_relat_1(B_126), A_127) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.55/1.56  tff(c_131, plain, (![A_127]: (v1_funct_2('#skF_5', '#skF_1', A_127) | ~r1_tarski(k2_relat_1('#skF_5'), A_127) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_128])).
% 3.55/1.56  tff(c_134, plain, (![A_128]: (v1_funct_2('#skF_5', '#skF_1', A_128) | ~r1_tarski(k2_relat_1('#skF_5'), A_128))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_42, c_131])).
% 3.55/1.56  tff(c_138, plain, (![A_4]: (v1_funct_2('#skF_5', '#skF_1', A_4) | ~v5_relat_1('#skF_5', A_4) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_6, c_134])).
% 3.55/1.56  tff(c_141, plain, (![A_4]: (v1_funct_2('#skF_5', '#skF_1', A_4) | ~v5_relat_1('#skF_5', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_138])).
% 3.55/1.56  tff(c_198, plain, (![A_134, B_135, C_136, D_137]: (m1_subset_1(k3_funct_2(A_134, B_135, C_136, D_137), B_135) | ~m1_subset_1(D_137, A_134) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_2(C_136, A_134, B_135) | ~v1_funct_1(C_136) | v1_xboole_0(A_134))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.55/1.56  tff(c_206, plain, (![D_137]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_3', '#skF_5', D_137), '#skF_3') | ~m1_subset_1(D_137, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_198])).
% 3.55/1.56  tff(c_218, plain, (![D_137]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_3', '#skF_5', D_137), '#skF_3') | ~m1_subset_1(D_137, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_206])).
% 3.55/1.56  tff(c_219, plain, (![D_137]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_3', '#skF_5', D_137), '#skF_3') | ~m1_subset_1(D_137, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_218])).
% 3.55/1.56  tff(c_234, plain, (~v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_219])).
% 3.55/1.56  tff(c_237, plain, (~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_141, c_234])).
% 3.55/1.56  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_237])).
% 3.55/1.56  tff(c_243, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_219])).
% 3.55/1.56  tff(c_204, plain, (![D_137]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_137), '#skF_1') | ~m1_subset_1(D_137, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_198])).
% 3.55/1.56  tff(c_214, plain, (![D_137]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_137), '#skF_1') | ~m1_subset_1(D_137, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_204])).
% 3.55/1.56  tff(c_215, plain, (![D_137]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_137), '#skF_1') | ~m1_subset_1(D_137, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_214])).
% 3.55/1.56  tff(c_408, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_372, c_215])).
% 3.55/1.56  tff(c_412, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_408])).
% 3.55/1.56  tff(c_22, plain, (![A_21, B_22, C_23, D_24]: (k3_funct_2(A_21, B_22, C_23, D_24)=k1_funct_1(C_23, D_24) | ~m1_subset_1(D_24, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.55/1.56  tff(c_417, plain, (![B_22, C_23]: (k3_funct_2('#skF_1', B_22, C_23, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_23, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_22))) | ~v1_funct_2(C_23, '#skF_1', B_22) | ~v1_funct_1(C_23) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_412, c_22])).
% 3.55/1.56  tff(c_442, plain, (![B_168, C_169]: (k3_funct_2('#skF_1', B_168, C_169, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_169, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_168))) | ~v1_funct_2(C_169, '#skF_1', B_168) | ~v1_funct_1(C_169))), inference(negUnitSimplification, [status(thm)], [c_52, c_417])).
% 3.55/1.56  tff(c_452, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_442])).
% 3.55/1.56  tff(c_459, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_243, c_452])).
% 3.55/1.56  tff(c_24, plain, (![A_25, B_33, C_37, D_39]: (k3_funct_2(A_25, B_33, C_37, D_39)=k7_partfun1(B_33, C_37, D_39) | ~m1_subset_1(D_39, A_25) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_25, B_33))) | ~v1_funct_2(C_37, A_25, B_33) | ~v1_funct_1(C_37) | v1_xboole_0(B_33) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.55/1.56  tff(c_415, plain, (![B_33, C_37]: (k3_funct_2('#skF_1', B_33, C_37, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_33, C_37, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_33))) | ~v1_funct_2(C_37, '#skF_1', B_33) | ~v1_funct_1(C_37) | v1_xboole_0(B_33) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_412, c_24])).
% 3.55/1.56  tff(c_557, plain, (![B_178, C_179]: (k3_funct_2('#skF_1', B_178, C_179, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_178, C_179, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_178))) | ~v1_funct_2(C_179, '#skF_1', B_178) | ~v1_funct_1(C_179) | v1_xboole_0(B_178))), inference(negUnitSimplification, [status(thm)], [c_52, c_415])).
% 3.55/1.56  tff(c_567, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_557])).
% 3.55/1.56  tff(c_574, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_243, c_459, c_567])).
% 3.55/1.56  tff(c_575, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_126, c_574])).
% 3.55/1.56  tff(c_34, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.55/1.56  tff(c_404, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_34])).
% 3.55/1.56  tff(c_576, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_404])).
% 3.55/1.56  tff(c_937, plain, (k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_931, c_576])).
% 3.55/1.56  tff(c_944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_372, c_937])).
% 3.55/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.56  
% 3.55/1.56  Inference rules
% 3.55/1.56  ----------------------
% 3.55/1.56  #Ref     : 0
% 3.55/1.56  #Sup     : 177
% 3.55/1.56  #Fact    : 0
% 3.55/1.56  #Define  : 0
% 3.55/1.56  #Split   : 6
% 3.55/1.56  #Chain   : 0
% 3.55/1.56  #Close   : 0
% 3.55/1.56  
% 3.55/1.56  Ordering : KBO
% 3.55/1.56  
% 3.55/1.56  Simplification rules
% 3.55/1.56  ----------------------
% 3.55/1.56  #Subsume      : 15
% 3.55/1.56  #Demod        : 117
% 3.55/1.56  #Tautology    : 36
% 3.55/1.56  #SimpNegUnit  : 31
% 3.55/1.56  #BackRed      : 2
% 3.55/1.57  
% 3.55/1.57  #Partial instantiations: 0
% 3.55/1.57  #Strategies tried      : 1
% 3.55/1.57  
% 3.55/1.57  Timing (in seconds)
% 3.55/1.57  ----------------------
% 3.55/1.57  Preprocessing        : 0.36
% 3.55/1.57  Parsing              : 0.19
% 3.55/1.57  CNF conversion       : 0.03
% 3.55/1.57  Main loop            : 0.43
% 3.55/1.57  Inferencing          : 0.15
% 3.55/1.57  Reduction            : 0.14
% 3.55/1.57  Demodulation         : 0.10
% 3.55/1.57  BG Simplification    : 0.03
% 3.55/1.57  Subsumption          : 0.08
% 3.55/1.57  Abstraction          : 0.03
% 3.55/1.57  MUC search           : 0.00
% 3.55/1.57  Cooper               : 0.00
% 3.55/1.57  Total                : 0.83
% 3.55/1.57  Index Insertion      : 0.00
% 3.55/1.57  Index Deletion       : 0.00
% 3.55/1.57  Index Matching       : 0.00
% 3.55/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
