%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:07 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 574 expanded)
%              Number of leaves         :   38 ( 216 expanded)
%              Depth                    :   19
%              Number of atoms          :  181 (1881 expanded)
%              Number of equality atoms :   27 ( 347 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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

tff(f_109,axiom,(
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

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_74,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_74])).

tff(c_63,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_67,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_63])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_120,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_124,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_120])).

tff(c_48,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_125,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_48])).

tff(c_135,plain,
    ( ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_141,plain,(
    ~ v5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_135])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_142,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_146,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_142])).

tff(c_202,plain,(
    ! [B_102,A_103,C_104] :
      ( k1_xboole_0 = B_102
      | k1_relset_1(A_103,B_102,C_104) = A_103
      | ~ v1_funct_2(C_104,A_103,B_102)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_205,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_202])).

tff(c_208,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_146,c_205])).

tff(c_209,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_242,plain,(
    ! [C_110,B_111] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_110),B_111,C_110),k1_relat_1(C_110))
      | m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_110),B_111)))
      | ~ v1_funct_1(C_110)
      | ~ v1_relat_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_248,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_1'('#skF_3',B_111,'#skF_5'),k1_relat_1('#skF_5'))
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_111)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_242])).

tff(c_257,plain,(
    ! [B_112] :
      ( r2_hidden('#skF_1'('#skF_3',B_112,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_112))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_56,c_209,c_209,c_248])).

tff(c_14,plain,(
    ! [C_14,B_13,A_12] :
      ( v5_relat_1(C_14,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_294,plain,(
    ! [B_113] :
      ( v5_relat_1('#skF_5',B_113)
      | r2_hidden('#skF_1'('#skF_3',B_113,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_257,c_14])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_298,plain,(
    ! [B_113] :
      ( m1_subset_1('#skF_1'('#skF_3',B_113,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_113) ) ),
    inference(resolution,[status(thm)],[c_294,c_6])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_342,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( k3_funct_2(A_126,B_127,C_128,D_129) = k1_funct_1(C_128,D_129)
      | ~ m1_subset_1(D_129,A_126)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(C_128,A_126,B_127)
      | ~ v1_funct_1(C_128)
      | v1_xboole_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_352,plain,(
    ! [B_127,C_128,B_113] :
      ( k3_funct_2('#skF_3',B_127,C_128,'#skF_1'('#skF_3',B_113,'#skF_5')) = k1_funct_1(C_128,'#skF_1'('#skF_3',B_113,'#skF_5'))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_127)))
      | ~ v1_funct_2(C_128,'#skF_3',B_127)
      | ~ v1_funct_1(C_128)
      | v1_xboole_0('#skF_3')
      | v5_relat_1('#skF_5',B_113) ) ),
    inference(resolution,[status(thm)],[c_298,c_342])).

tff(c_418,plain,(
    ! [B_131,C_132,B_133] :
      ( k3_funct_2('#skF_3',B_131,C_132,'#skF_1'('#skF_3',B_133,'#skF_5')) = k1_funct_1(C_132,'#skF_1'('#skF_3',B_133,'#skF_5'))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_131)))
      | ~ v1_funct_2(C_132,'#skF_3',B_131)
      | ~ v1_funct_1(C_132)
      | v5_relat_1('#skF_5',B_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_352])).

tff(c_424,plain,(
    ! [B_133] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_133,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_133,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v5_relat_1('#skF_5',B_133) ) ),
    inference(resolution,[status(thm)],[c_52,c_418])).

tff(c_450,plain,(
    ! [B_137] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_137,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_137,'#skF_5'))
      | v5_relat_1('#skF_5',B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_424])).

tff(c_50,plain,(
    ! [E_43] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_43),'#skF_2')
      | ~ m1_subset_1(E_43,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_469,plain,(
    ! [B_139] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_139,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_139,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_50])).

tff(c_234,plain,(
    ! [C_106,B_107] :
      ( ~ r2_hidden(k1_funct_1(C_106,'#skF_1'(k1_relat_1(C_106),B_107,C_106)),B_107)
      | v1_funct_2(C_106,k1_relat_1(C_106),B_107)
      | ~ v1_funct_1(C_106)
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_237,plain,(
    ! [B_107] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_107,'#skF_5')),B_107)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_107)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_234])).

tff(c_239,plain,(
    ! [B_107] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_107,'#skF_5')),B_107)
      | v1_funct_2('#skF_5','#skF_3',B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_56,c_209,c_237])).

tff(c_477,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_469,c_239])).

tff(c_486,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_477])).

tff(c_488,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_497,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_298,c_488])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_497])).

tff(c_508,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_306,plain,(
    ! [C_117,B_118] :
      ( ~ r2_hidden(k1_funct_1(C_117,'#skF_1'(k1_relat_1(C_117),B_118,C_117)),B_118)
      | m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_117),B_118)))
      | ~ v1_funct_1(C_117)
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_309,plain,(
    ! [B_118] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_118,'#skF_5')),B_118)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_118)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_306])).

tff(c_311,plain,(
    ! [B_118] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_118,'#skF_5')),B_118)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_118))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_56,c_209,c_309])).

tff(c_473,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_469,c_311])).

tff(c_483,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_473])).

tff(c_535,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_483])).

tff(c_562,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_535,c_14])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_562])).

tff(c_590,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(A_61,C_62)
      | ~ r1_tarski(B_63,C_62)
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_64,A_65] :
      ( r1_tarski(A_64,A_65)
      | ~ r1_tarski(A_64,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_89])).

tff(c_103,plain,(
    ! [B_8,A_65] :
      ( r1_tarski(k2_relat_1(B_8),A_65)
      | ~ v5_relat_1(B_8,k1_xboole_0)
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_132,plain,
    ( ~ v5_relat_1('#skF_5',k1_xboole_0)
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_125])).

tff(c_138,plain,(
    ~ v5_relat_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_132])).

tff(c_600,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_138])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:56:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.61  
% 3.07/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.07/1.61  
% 3.07/1.61  %Foreground sorts:
% 3.07/1.61  
% 3.07/1.61  
% 3.07/1.61  %Background operators:
% 3.07/1.61  
% 3.07/1.61  
% 3.07/1.61  %Foreground operators:
% 3.07/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.07/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.07/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.07/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.07/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.07/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.07/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.61  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.07/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.61  
% 3.22/1.63  tff(f_131, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 3.22/1.63  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.22/1.63  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.22/1.63  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.22/1.63  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.22/1.63  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.22/1.63  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.22/1.63  tff(f_109, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 3.22/1.63  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.22/1.63  tff(f_92, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.22/1.63  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.22/1.63  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.22/1.63  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.63  tff(c_74, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.22/1.63  tff(c_78, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_74])).
% 3.22/1.63  tff(c_63, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.63  tff(c_67, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_63])).
% 3.22/1.63  tff(c_10, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.22/1.63  tff(c_120, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.22/1.63  tff(c_124, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_120])).
% 3.22/1.63  tff(c_48, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.63  tff(c_125, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_48])).
% 3.22/1.63  tff(c_135, plain, (~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_125])).
% 3.22/1.63  tff(c_141, plain, (~v5_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_135])).
% 3.22/1.63  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.63  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.63  tff(c_142, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.22/1.63  tff(c_146, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_142])).
% 3.22/1.63  tff(c_202, plain, (![B_102, A_103, C_104]: (k1_xboole_0=B_102 | k1_relset_1(A_103, B_102, C_104)=A_103 | ~v1_funct_2(C_104, A_103, B_102) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.22/1.63  tff(c_205, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_202])).
% 3.22/1.63  tff(c_208, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_146, c_205])).
% 3.22/1.63  tff(c_209, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_208])).
% 3.22/1.63  tff(c_242, plain, (![C_110, B_111]: (r2_hidden('#skF_1'(k1_relat_1(C_110), B_111, C_110), k1_relat_1(C_110)) | m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_110), B_111))) | ~v1_funct_1(C_110) | ~v1_relat_1(C_110))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.22/1.63  tff(c_248, plain, (![B_111]: (r2_hidden('#skF_1'('#skF_3', B_111, '#skF_5'), k1_relat_1('#skF_5')) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_111))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_242])).
% 3.22/1.63  tff(c_257, plain, (![B_112]: (r2_hidden('#skF_1'('#skF_3', B_112, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_112))))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_56, c_209, c_209, c_248])).
% 3.22/1.63  tff(c_14, plain, (![C_14, B_13, A_12]: (v5_relat_1(C_14, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.22/1.63  tff(c_294, plain, (![B_113]: (v5_relat_1('#skF_5', B_113) | r2_hidden('#skF_1'('#skF_3', B_113, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_257, c_14])).
% 3.22/1.63  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.63  tff(c_298, plain, (![B_113]: (m1_subset_1('#skF_1'('#skF_3', B_113, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_113))), inference(resolution, [status(thm)], [c_294, c_6])).
% 3.22/1.63  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.63  tff(c_342, plain, (![A_126, B_127, C_128, D_129]: (k3_funct_2(A_126, B_127, C_128, D_129)=k1_funct_1(C_128, D_129) | ~m1_subset_1(D_129, A_126) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(C_128, A_126, B_127) | ~v1_funct_1(C_128) | v1_xboole_0(A_126))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.63  tff(c_352, plain, (![B_127, C_128, B_113]: (k3_funct_2('#skF_3', B_127, C_128, '#skF_1'('#skF_3', B_113, '#skF_5'))=k1_funct_1(C_128, '#skF_1'('#skF_3', B_113, '#skF_5')) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_127))) | ~v1_funct_2(C_128, '#skF_3', B_127) | ~v1_funct_1(C_128) | v1_xboole_0('#skF_3') | v5_relat_1('#skF_5', B_113))), inference(resolution, [status(thm)], [c_298, c_342])).
% 3.22/1.63  tff(c_418, plain, (![B_131, C_132, B_133]: (k3_funct_2('#skF_3', B_131, C_132, '#skF_1'('#skF_3', B_133, '#skF_5'))=k1_funct_1(C_132, '#skF_1'('#skF_3', B_133, '#skF_5')) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_131))) | ~v1_funct_2(C_132, '#skF_3', B_131) | ~v1_funct_1(C_132) | v5_relat_1('#skF_5', B_133))), inference(negUnitSimplification, [status(thm)], [c_60, c_352])).
% 3.22/1.63  tff(c_424, plain, (![B_133]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_133, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_133, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v5_relat_1('#skF_5', B_133))), inference(resolution, [status(thm)], [c_52, c_418])).
% 3.22/1.63  tff(c_450, plain, (![B_137]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_137, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_137, '#skF_5')) | v5_relat_1('#skF_5', B_137))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_424])).
% 3.22/1.63  tff(c_50, plain, (![E_43]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_43), '#skF_2') | ~m1_subset_1(E_43, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.63  tff(c_469, plain, (![B_139]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_139, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_139, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_139))), inference(superposition, [status(thm), theory('equality')], [c_450, c_50])).
% 3.22/1.63  tff(c_234, plain, (![C_106, B_107]: (~r2_hidden(k1_funct_1(C_106, '#skF_1'(k1_relat_1(C_106), B_107, C_106)), B_107) | v1_funct_2(C_106, k1_relat_1(C_106), B_107) | ~v1_funct_1(C_106) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.22/1.63  tff(c_237, plain, (![B_107]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_107, '#skF_5')), B_107) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_107) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_234])).
% 3.22/1.63  tff(c_239, plain, (![B_107]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_107, '#skF_5')), B_107) | v1_funct_2('#skF_5', '#skF_3', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_56, c_209, c_237])).
% 3.22/1.63  tff(c_477, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_469, c_239])).
% 3.22/1.63  tff(c_486, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_141, c_477])).
% 3.22/1.63  tff(c_488, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_486])).
% 3.22/1.63  tff(c_497, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_298, c_488])).
% 3.22/1.63  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_497])).
% 3.22/1.63  tff(c_508, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_486])).
% 3.22/1.63  tff(c_306, plain, (![C_117, B_118]: (~r2_hidden(k1_funct_1(C_117, '#skF_1'(k1_relat_1(C_117), B_118, C_117)), B_118) | m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_117), B_118))) | ~v1_funct_1(C_117) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.22/1.63  tff(c_309, plain, (![B_118]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_118, '#skF_5')), B_118) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_118))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_306])).
% 3.22/1.63  tff(c_311, plain, (![B_118]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_118, '#skF_5')), B_118) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_118))))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_56, c_209, c_309])).
% 3.22/1.63  tff(c_473, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_469, c_311])).
% 3.22/1.63  tff(c_483, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_141, c_473])).
% 3.22/1.63  tff(c_535, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_508, c_483])).
% 3.22/1.63  tff(c_562, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_535, c_14])).
% 3.22/1.63  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_562])).
% 3.22/1.63  tff(c_590, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_208])).
% 3.22/1.63  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.63  tff(c_89, plain, (![A_61, C_62, B_63]: (r1_tarski(A_61, C_62) | ~r1_tarski(B_63, C_62) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.63  tff(c_96, plain, (![A_64, A_65]: (r1_tarski(A_64, A_65) | ~r1_tarski(A_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_89])).
% 3.22/1.63  tff(c_103, plain, (![B_8, A_65]: (r1_tarski(k2_relat_1(B_8), A_65) | ~v5_relat_1(B_8, k1_xboole_0) | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_10, c_96])).
% 3.22/1.63  tff(c_132, plain, (~v5_relat_1('#skF_5', k1_xboole_0) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_103, c_125])).
% 3.22/1.63  tff(c_138, plain, (~v5_relat_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_132])).
% 3.22/1.63  tff(c_600, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_590, c_138])).
% 3.22/1.63  tff(c_607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_600])).
% 3.22/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.63  
% 3.22/1.63  Inference rules
% 3.22/1.63  ----------------------
% 3.22/1.63  #Ref     : 0
% 3.22/1.63  #Sup     : 108
% 3.22/1.63  #Fact    : 0
% 3.22/1.63  #Define  : 0
% 3.22/1.63  #Split   : 4
% 3.22/1.63  #Chain   : 0
% 3.22/1.63  #Close   : 0
% 3.22/1.63  
% 3.22/1.63  Ordering : KBO
% 3.22/1.63  
% 3.22/1.63  Simplification rules
% 3.22/1.63  ----------------------
% 3.22/1.63  #Subsume      : 17
% 3.22/1.63  #Demod        : 106
% 3.22/1.63  #Tautology    : 23
% 3.22/1.63  #SimpNegUnit  : 9
% 3.22/1.63  #BackRed      : 15
% 3.22/1.63  
% 3.22/1.63  #Partial instantiations: 0
% 3.22/1.63  #Strategies tried      : 1
% 3.22/1.63  
% 3.22/1.63  Timing (in seconds)
% 3.22/1.63  ----------------------
% 3.22/1.63  Preprocessing        : 0.48
% 3.22/1.63  Parsing              : 0.28
% 3.22/1.63  CNF conversion       : 0.03
% 3.22/1.63  Main loop            : 0.33
% 3.22/1.63  Inferencing          : 0.12
% 3.22/1.63  Reduction            : 0.10
% 3.22/1.63  Demodulation         : 0.07
% 3.22/1.63  BG Simplification    : 0.02
% 3.22/1.63  Subsumption          : 0.06
% 3.22/1.63  Abstraction          : 0.02
% 3.22/1.63  MUC search           : 0.00
% 3.22/1.63  Cooper               : 0.00
% 3.22/1.63  Total                : 0.85
% 3.22/1.63  Index Insertion      : 0.00
% 3.22/1.63  Index Deletion       : 0.00
% 3.22/1.63  Index Matching       : 0.00
% 3.22/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
