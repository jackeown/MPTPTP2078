%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:07 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :  114 (1008 expanded)
%              Number of leaves         :   38 ( 368 expanded)
%              Depth                    :   25
%              Number of atoms          :  216 (3555 expanded)
%              Number of equality atoms :   37 ( 734 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_158,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_172,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_158])).

tff(c_50,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_173,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_50])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_102,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_116,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_202,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_216,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_202])).

tff(c_506,plain,(
    ! [B_112,A_113,C_114] :
      ( k1_xboole_0 = B_112
      | k1_relset_1(A_113,B_112,C_114) = A_113
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_521,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_506])).

tff(c_527,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_216,c_521])).

tff(c_585,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_527])).

tff(c_44,plain,(
    ! [C_33,B_32] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_33),B_32,C_33),k1_relat_1(C_33))
      | v1_funct_2(C_33,k1_relat_1(C_33),B_32)
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_593,plain,(
    ! [B_32] :
      ( r2_hidden('#skF_2'(k1_relat_1('#skF_6'),B_32,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6',k1_relat_1('#skF_6'),B_32)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_44])).

tff(c_664,plain,(
    ! [B_126] :
      ( r2_hidden('#skF_2'('#skF_4',B_126,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_58,c_585,c_585,c_593])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_675,plain,(
    ! [B_126] :
      ( m1_subset_1('#skF_2'('#skF_4',B_126,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_126) ) ),
    inference(resolution,[status(thm)],[c_664,c_8])).

tff(c_1006,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k3_funct_2(A_160,B_161,C_162,D_163) = k1_funct_1(C_162,D_163)
      | ~ m1_subset_1(D_163,A_160)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_2(C_162,A_160,B_161)
      | ~ v1_funct_1(C_162)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1014,plain,(
    ! [B_161,C_162,B_126] :
      ( k3_funct_2('#skF_4',B_161,C_162,'#skF_2'('#skF_4',B_126,'#skF_6')) = k1_funct_1(C_162,'#skF_2'('#skF_4',B_126,'#skF_6'))
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_161)))
      | ~ v1_funct_2(C_162,'#skF_4',B_161)
      | ~ v1_funct_1(C_162)
      | v1_xboole_0('#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_126) ) ),
    inference(resolution,[status(thm)],[c_675,c_1006])).

tff(c_1083,plain,(
    ! [B_166,C_167,B_168] :
      ( k3_funct_2('#skF_4',B_166,C_167,'#skF_2'('#skF_4',B_168,'#skF_6')) = k1_funct_1(C_167,'#skF_2'('#skF_4',B_168,'#skF_6'))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_166)))
      | ~ v1_funct_2(C_167,'#skF_4',B_166)
      | ~ v1_funct_1(C_167)
      | v1_funct_2('#skF_6','#skF_4',B_168) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1014])).

tff(c_1099,plain,(
    ! [B_168] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4',B_168,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4',B_168,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_funct_2('#skF_6','#skF_4',B_168) ) ),
    inference(resolution,[status(thm)],[c_54,c_1083])).

tff(c_1748,plain,(
    ! [B_225] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4',B_225,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4',B_225,'#skF_6'))
      | v1_funct_2('#skF_6','#skF_4',B_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1099])).

tff(c_52,plain,(
    ! [E_46] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_46),'#skF_3')
      | ~ m1_subset_1(E_46,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1850,plain,(
    ! [B_231] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_231,'#skF_6')),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_231,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1748,c_52])).

tff(c_682,plain,(
    ! [C_129,B_130] :
      ( ~ r2_hidden(k1_funct_1(C_129,'#skF_2'(k1_relat_1(C_129),B_130,C_129)),B_130)
      | v1_funct_2(C_129,k1_relat_1(C_129),B_130)
      | ~ v1_funct_1(C_129)
      | ~ v1_relat_1(C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_685,plain,(
    ! [B_130] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_130,'#skF_6')),B_130)
      | v1_funct_2('#skF_6',k1_relat_1('#skF_6'),B_130)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_682])).

tff(c_687,plain,(
    ! [B_130] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_130,'#skF_6')),B_130)
      | v1_funct_2('#skF_6','#skF_4',B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_58,c_585,c_685])).

tff(c_1869,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4')
    | v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1850,c_687])).

tff(c_1873,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1869])).

tff(c_774,plain,(
    ! [C_142,B_143] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_142),B_143,C_142),k1_relat_1(C_142))
      | m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_142),B_143)))
      | ~ v1_funct_1(C_142)
      | ~ v1_relat_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_786,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_2'('#skF_4',B_143,'#skF_6'),k1_relat_1('#skF_6'))
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_143)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_774])).

tff(c_797,plain,(
    ! [B_144] :
      ( r2_hidden('#skF_2'('#skF_4',B_144,'#skF_6'),'#skF_4')
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_144))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_58,c_585,c_585,c_786])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] :
      ( k2_relset_1(A_21,B_22,C_23) = k2_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_906,plain,(
    ! [B_153] :
      ( k2_relset_1('#skF_4',B_153,'#skF_6') = k2_relat_1('#skF_6')
      | r2_hidden('#skF_2'('#skF_4',B_153,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_797,c_22])).

tff(c_917,plain,(
    ! [B_153] :
      ( m1_subset_1('#skF_2'('#skF_4',B_153,'#skF_6'),'#skF_4')
      | k2_relset_1('#skF_4',B_153,'#skF_6') = k2_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_906,c_8])).

tff(c_1883,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_917,c_1873])).

tff(c_244,plain,(
    ! [A_91,B_92,C_93] :
      ( m1_subset_1(k2_relset_1(A_91,B_92,C_93),k1_zfmisc_1(B_92))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_269,plain,(
    ! [A_91,B_92,C_93] :
      ( r1_tarski(k2_relset_1(A_91,B_92,C_93),B_92)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(resolution,[status(thm)],[c_244,c_10])).

tff(c_919,plain,(
    ! [B_154] :
      ( r1_tarski(k2_relset_1('#skF_4',B_154,'#skF_6'),B_154)
      | r2_hidden('#skF_2'('#skF_4',B_154,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_797,c_269])).

tff(c_951,plain,(
    ! [B_154] :
      ( m1_subset_1('#skF_2'('#skF_4',B_154,'#skF_6'),'#skF_4')
      | r1_tarski(k2_relset_1('#skF_4',B_154,'#skF_6'),B_154) ) ),
    inference(resolution,[status(thm)],[c_919,c_8])).

tff(c_1896,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4')
    | r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1883,c_951])).

tff(c_1908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_1873,c_1896])).

tff(c_1910,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1869])).

tff(c_36,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( k3_funct_2(A_27,B_28,C_29,D_30) = k1_funct_1(C_29,D_30)
      | ~ m1_subset_1(D_30,A_27)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1946,plain,(
    ! [B_28,C_29] :
      ( k3_funct_2('#skF_4',B_28,C_29,'#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1(C_29,'#skF_2'('#skF_4','#skF_3','#skF_6'))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_28)))
      | ~ v1_funct_2(C_29,'#skF_4',B_28)
      | ~ v1_funct_1(C_29)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1910,c_36])).

tff(c_1952,plain,(
    ! [B_236,C_237] :
      ( k3_funct_2('#skF_4',B_236,C_237,'#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1(C_237,'#skF_2'('#skF_4','#skF_3','#skF_6'))
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_236)))
      | ~ v1_funct_2(C_237,'#skF_4',B_236)
      | ~ v1_funct_1(C_237) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1946])).

tff(c_1980,plain,
    ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_1952])).

tff(c_1996,plain,(
    k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1980])).

tff(c_2009,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1996,c_52])).

tff(c_2022,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_2009])).

tff(c_900,plain,(
    ! [C_151,B_152] :
      ( ~ r2_hidden(k1_funct_1(C_151,'#skF_2'(k1_relat_1(C_151),B_152,C_151)),B_152)
      | m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_151),B_152)))
      | ~ v1_funct_1(C_151)
      | ~ v1_relat_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_903,plain,(
    ! [B_152] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_152,'#skF_6')),B_152)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_152)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_900])).

tff(c_905,plain,(
    ! [B_152] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_152,'#skF_6')),B_152)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_152))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_58,c_585,c_903])).

tff(c_2046,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2022,c_905])).

tff(c_2113,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2046,c_10])).

tff(c_2110,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2046,c_22])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_691,plain,(
    ! [A_131,B_132,C_133] :
      ( r1_tarski(k2_relset_1(A_131,B_132,C_133),B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(resolution,[status(thm)],[c_244,c_10])).

tff(c_709,plain,(
    ! [A_131,B_132,A_8] :
      ( r1_tarski(k2_relset_1(A_131,B_132,A_8),B_132)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_131,B_132)) ) ),
    inference(resolution,[status(thm)],[c_12,c_691])).

tff(c_2188,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_3')
    | ~ r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_709])).

tff(c_2198,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2113,c_2188])).

tff(c_2200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_2198])).

tff(c_2201,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [B_53,A_54] :
      ( ~ r1_tarski(B_53,A_54)
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    ! [A_56] :
      ( ~ r1_tarski(A_56,'#skF_1'(A_56))
      | v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_4,c_75])).

tff(c_86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_2214,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2201,c_86])).

tff(c_2217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.83  
% 4.49/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.84  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.49/1.84  
% 4.49/1.84  %Foreground sorts:
% 4.49/1.84  
% 4.49/1.84  
% 4.49/1.84  %Background operators:
% 4.49/1.84  
% 4.49/1.84  
% 4.49/1.84  %Foreground operators:
% 4.49/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.49/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.49/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.49/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.49/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.49/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.49/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.49/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.49/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.49/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.49/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.49/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.49/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.49/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.49/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.49/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.49/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.49/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.49/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.49/1.84  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.49/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.49/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.49/1.84  
% 4.49/1.86  tff(f_132, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 4.49/1.86  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.49/1.86  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.49/1.86  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.49/1.86  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.49/1.86  tff(f_110, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 4.49/1.86  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.49/1.86  tff(f_93, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.49/1.86  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.49/1.86  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.49/1.86  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.49/1.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.49/1.86  tff(f_46, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.49/1.86  tff(c_60, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.49/1.86  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.49/1.86  tff(c_158, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.49/1.86  tff(c_172, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_158])).
% 4.49/1.86  tff(c_50, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.49/1.86  tff(c_173, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_50])).
% 4.49/1.86  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.49/1.86  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.49/1.86  tff(c_62, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.49/1.86  tff(c_102, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.49/1.86  tff(c_116, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_102])).
% 4.49/1.86  tff(c_202, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.49/1.86  tff(c_216, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_202])).
% 4.49/1.86  tff(c_506, plain, (![B_112, A_113, C_114]: (k1_xboole_0=B_112 | k1_relset_1(A_113, B_112, C_114)=A_113 | ~v1_funct_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.49/1.86  tff(c_521, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_506])).
% 4.49/1.86  tff(c_527, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_216, c_521])).
% 4.49/1.86  tff(c_585, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_527])).
% 4.49/1.86  tff(c_44, plain, (![C_33, B_32]: (r2_hidden('#skF_2'(k1_relat_1(C_33), B_32, C_33), k1_relat_1(C_33)) | v1_funct_2(C_33, k1_relat_1(C_33), B_32) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.49/1.86  tff(c_593, plain, (![B_32]: (r2_hidden('#skF_2'(k1_relat_1('#skF_6'), B_32, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', k1_relat_1('#skF_6'), B_32) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_585, c_44])).
% 4.49/1.86  tff(c_664, plain, (![B_126]: (r2_hidden('#skF_2'('#skF_4', B_126, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_126))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_58, c_585, c_585, c_593])).
% 4.49/1.86  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.49/1.86  tff(c_675, plain, (![B_126]: (m1_subset_1('#skF_2'('#skF_4', B_126, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_126))), inference(resolution, [status(thm)], [c_664, c_8])).
% 4.49/1.86  tff(c_1006, plain, (![A_160, B_161, C_162, D_163]: (k3_funct_2(A_160, B_161, C_162, D_163)=k1_funct_1(C_162, D_163) | ~m1_subset_1(D_163, A_160) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_2(C_162, A_160, B_161) | ~v1_funct_1(C_162) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.49/1.86  tff(c_1014, plain, (![B_161, C_162, B_126]: (k3_funct_2('#skF_4', B_161, C_162, '#skF_2'('#skF_4', B_126, '#skF_6'))=k1_funct_1(C_162, '#skF_2'('#skF_4', B_126, '#skF_6')) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_161))) | ~v1_funct_2(C_162, '#skF_4', B_161) | ~v1_funct_1(C_162) | v1_xboole_0('#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_126))), inference(resolution, [status(thm)], [c_675, c_1006])).
% 4.49/1.86  tff(c_1083, plain, (![B_166, C_167, B_168]: (k3_funct_2('#skF_4', B_166, C_167, '#skF_2'('#skF_4', B_168, '#skF_6'))=k1_funct_1(C_167, '#skF_2'('#skF_4', B_168, '#skF_6')) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_166))) | ~v1_funct_2(C_167, '#skF_4', B_166) | ~v1_funct_1(C_167) | v1_funct_2('#skF_6', '#skF_4', B_168))), inference(negUnitSimplification, [status(thm)], [c_62, c_1014])).
% 4.49/1.86  tff(c_1099, plain, (![B_168]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', B_168, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_168, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_funct_2('#skF_6', '#skF_4', B_168))), inference(resolution, [status(thm)], [c_54, c_1083])).
% 4.49/1.86  tff(c_1748, plain, (![B_225]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', B_225, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_225, '#skF_6')) | v1_funct_2('#skF_6', '#skF_4', B_225))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1099])).
% 4.49/1.86  tff(c_52, plain, (![E_46]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_46), '#skF_3') | ~m1_subset_1(E_46, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.49/1.86  tff(c_1850, plain, (![B_231]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_231, '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', B_231, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_231))), inference(superposition, [status(thm), theory('equality')], [c_1748, c_52])).
% 4.49/1.86  tff(c_682, plain, (![C_129, B_130]: (~r2_hidden(k1_funct_1(C_129, '#skF_2'(k1_relat_1(C_129), B_130, C_129)), B_130) | v1_funct_2(C_129, k1_relat_1(C_129), B_130) | ~v1_funct_1(C_129) | ~v1_relat_1(C_129))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.49/1.86  tff(c_685, plain, (![B_130]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_130, '#skF_6')), B_130) | v1_funct_2('#skF_6', k1_relat_1('#skF_6'), B_130) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_585, c_682])).
% 4.49/1.86  tff(c_687, plain, (![B_130]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_130, '#skF_6')), B_130) | v1_funct_2('#skF_6', '#skF_4', B_130))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_58, c_585, c_685])).
% 4.49/1.86  tff(c_1869, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1850, c_687])).
% 4.49/1.86  tff(c_1873, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1869])).
% 4.49/1.86  tff(c_774, plain, (![C_142, B_143]: (r2_hidden('#skF_2'(k1_relat_1(C_142), B_143, C_142), k1_relat_1(C_142)) | m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_142), B_143))) | ~v1_funct_1(C_142) | ~v1_relat_1(C_142))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.49/1.86  tff(c_786, plain, (![B_143]: (r2_hidden('#skF_2'('#skF_4', B_143, '#skF_6'), k1_relat_1('#skF_6')) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_143))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_585, c_774])).
% 4.49/1.86  tff(c_797, plain, (![B_144]: (r2_hidden('#skF_2'('#skF_4', B_144, '#skF_6'), '#skF_4') | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_144))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_58, c_585, c_585, c_786])).
% 4.49/1.86  tff(c_22, plain, (![A_21, B_22, C_23]: (k2_relset_1(A_21, B_22, C_23)=k2_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.49/1.86  tff(c_906, plain, (![B_153]: (k2_relset_1('#skF_4', B_153, '#skF_6')=k2_relat_1('#skF_6') | r2_hidden('#skF_2'('#skF_4', B_153, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_797, c_22])).
% 4.49/1.86  tff(c_917, plain, (![B_153]: (m1_subset_1('#skF_2'('#skF_4', B_153, '#skF_6'), '#skF_4') | k2_relset_1('#skF_4', B_153, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_906, c_8])).
% 4.49/1.86  tff(c_1883, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_917, c_1873])).
% 4.49/1.86  tff(c_244, plain, (![A_91, B_92, C_93]: (m1_subset_1(k2_relset_1(A_91, B_92, C_93), k1_zfmisc_1(B_92)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.49/1.86  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.49/1.86  tff(c_269, plain, (![A_91, B_92, C_93]: (r1_tarski(k2_relset_1(A_91, B_92, C_93), B_92) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(resolution, [status(thm)], [c_244, c_10])).
% 4.49/1.86  tff(c_919, plain, (![B_154]: (r1_tarski(k2_relset_1('#skF_4', B_154, '#skF_6'), B_154) | r2_hidden('#skF_2'('#skF_4', B_154, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_797, c_269])).
% 4.49/1.86  tff(c_951, plain, (![B_154]: (m1_subset_1('#skF_2'('#skF_4', B_154, '#skF_6'), '#skF_4') | r1_tarski(k2_relset_1('#skF_4', B_154, '#skF_6'), B_154))), inference(resolution, [status(thm)], [c_919, c_8])).
% 4.49/1.86  tff(c_1896, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4') | r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1883, c_951])).
% 4.49/1.86  tff(c_1908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_1873, c_1896])).
% 4.49/1.86  tff(c_1910, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_1869])).
% 4.49/1.86  tff(c_36, plain, (![A_27, B_28, C_29, D_30]: (k3_funct_2(A_27, B_28, C_29, D_30)=k1_funct_1(C_29, D_30) | ~m1_subset_1(D_30, A_27) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.49/1.86  tff(c_1946, plain, (![B_28, C_29]: (k3_funct_2('#skF_4', B_28, C_29, '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1(C_29, '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_28))) | ~v1_funct_2(C_29, '#skF_4', B_28) | ~v1_funct_1(C_29) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_1910, c_36])).
% 4.49/1.86  tff(c_1952, plain, (![B_236, C_237]: (k3_funct_2('#skF_4', B_236, C_237, '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1(C_237, '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_236))) | ~v1_funct_2(C_237, '#skF_4', B_236) | ~v1_funct_1(C_237))), inference(negUnitSimplification, [status(thm)], [c_62, c_1946])).
% 4.49/1.86  tff(c_1980, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_1952])).
% 4.49/1.86  tff(c_1996, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1980])).
% 4.49/1.86  tff(c_2009, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1996, c_52])).
% 4.49/1.86  tff(c_2022, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_2009])).
% 4.49/1.86  tff(c_900, plain, (![C_151, B_152]: (~r2_hidden(k1_funct_1(C_151, '#skF_2'(k1_relat_1(C_151), B_152, C_151)), B_152) | m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_151), B_152))) | ~v1_funct_1(C_151) | ~v1_relat_1(C_151))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.49/1.86  tff(c_903, plain, (![B_152]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_152, '#skF_6')), B_152) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_152))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_585, c_900])).
% 4.49/1.86  tff(c_905, plain, (![B_152]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_152, '#skF_6')), B_152) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_152))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_58, c_585, c_903])).
% 4.49/1.86  tff(c_2046, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_2022, c_905])).
% 4.49/1.86  tff(c_2113, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2046, c_10])).
% 4.49/1.86  tff(c_2110, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2046, c_22])).
% 4.49/1.86  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.49/1.86  tff(c_691, plain, (![A_131, B_132, C_133]: (r1_tarski(k2_relset_1(A_131, B_132, C_133), B_132) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(resolution, [status(thm)], [c_244, c_10])).
% 4.49/1.86  tff(c_709, plain, (![A_131, B_132, A_8]: (r1_tarski(k2_relset_1(A_131, B_132, A_8), B_132) | ~r1_tarski(A_8, k2_zfmisc_1(A_131, B_132)))), inference(resolution, [status(thm)], [c_12, c_691])).
% 4.49/1.86  tff(c_2188, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_3') | ~r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2110, c_709])).
% 4.49/1.86  tff(c_2198, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2113, c_2188])).
% 4.49/1.86  tff(c_2200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_2198])).
% 4.49/1.86  tff(c_2201, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_527])).
% 4.49/1.86  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.49/1.86  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.49/1.86  tff(c_75, plain, (![B_53, A_54]: (~r1_tarski(B_53, A_54) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.49/1.86  tff(c_81, plain, (![A_56]: (~r1_tarski(A_56, '#skF_1'(A_56)) | v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_4, c_75])).
% 4.49/1.86  tff(c_86, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_81])).
% 4.49/1.86  tff(c_2214, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2201, c_86])).
% 4.49/1.86  tff(c_2217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2214])).
% 4.49/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.86  
% 4.49/1.86  Inference rules
% 4.49/1.86  ----------------------
% 4.49/1.86  #Ref     : 0
% 4.49/1.86  #Sup     : 437
% 4.49/1.86  #Fact    : 0
% 4.49/1.86  #Define  : 0
% 4.49/1.86  #Split   : 7
% 4.49/1.86  #Chain   : 0
% 4.49/1.86  #Close   : 0
% 4.49/1.86  
% 4.49/1.86  Ordering : KBO
% 4.49/1.86  
% 4.49/1.86  Simplification rules
% 4.49/1.86  ----------------------
% 4.49/1.86  #Subsume      : 82
% 4.49/1.86  #Demod        : 311
% 4.49/1.86  #Tautology    : 103
% 4.49/1.86  #SimpNegUnit  : 22
% 4.49/1.86  #BackRed      : 27
% 4.49/1.86  
% 4.49/1.86  #Partial instantiations: 0
% 4.49/1.86  #Strategies tried      : 1
% 4.49/1.86  
% 4.49/1.86  Timing (in seconds)
% 4.49/1.86  ----------------------
% 4.49/1.86  Preprocessing        : 0.36
% 4.49/1.86  Parsing              : 0.19
% 4.49/1.86  CNF conversion       : 0.03
% 4.49/1.86  Main loop            : 0.64
% 4.49/1.86  Inferencing          : 0.23
% 4.49/1.86  Reduction            : 0.21
% 4.49/1.86  Demodulation         : 0.15
% 4.49/1.86  BG Simplification    : 0.03
% 4.49/1.86  Subsumption          : 0.10
% 4.49/1.86  Abstraction          : 0.04
% 4.49/1.86  MUC search           : 0.00
% 4.49/1.86  Cooper               : 0.00
% 4.49/1.86  Total                : 1.05
% 4.49/1.86  Index Insertion      : 0.00
% 4.49/1.86  Index Deletion       : 0.00
% 4.49/1.86  Index Matching       : 0.00
% 4.49/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
