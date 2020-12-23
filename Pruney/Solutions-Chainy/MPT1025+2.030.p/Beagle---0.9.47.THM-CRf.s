%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:34 EST 2020

% Result     : Theorem 5.72s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 224 expanded)
%              Number of leaves         :   47 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  163 ( 530 expanded)
%              Number of equality atoms :   38 ( 111 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_57,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_92,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_877,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k7_relset_1(A_167,B_168,C_169,D_170) = k9_relat_1(C_169,D_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_888,plain,(
    ! [D_170] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_170) = k9_relat_1('#skF_9',D_170) ),
    inference(resolution,[status(thm)],[c_92,c_877])).

tff(c_90,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_890,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_90])).

tff(c_963,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( m1_subset_1(k7_relset_1(A_178,B_179,C_180,D_181),k1_zfmisc_1(B_179))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_984,plain,(
    ! [D_170] :
      ( m1_subset_1(k9_relat_1('#skF_9',D_170),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_963])).

tff(c_992,plain,(
    ! [D_182] : m1_subset_1(k9_relat_1('#skF_9',D_182),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_984])).

tff(c_48,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_129,plain,(
    ! [A_69,B_70] :
      ( r2_hidden(A_69,B_70)
      | v1_xboole_0(B_70)
      | ~ m1_subset_1(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_133,plain,(
    ! [A_69,A_13] :
      ( r1_tarski(A_69,A_13)
      | v1_xboole_0(k1_zfmisc_1(A_13))
      | ~ m1_subset_1(A_69,k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_129,c_36])).

tff(c_139,plain,(
    ! [A_69,A_13] :
      ( r1_tarski(A_69,A_13)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(A_13)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_133])).

tff(c_997,plain,(
    ! [D_183] : r1_tarski(k9_relat_1('#skF_9',D_183),'#skF_7') ),
    inference(resolution,[status(thm)],[c_992,c_139])).

tff(c_32,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1002,plain,(
    ! [D_184] : k2_xboole_0(k9_relat_1('#skF_9',D_184),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_997,c_32])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1070,plain,(
    ! [D_189,D_190] :
      ( ~ r2_hidden(D_189,k9_relat_1('#skF_9',D_190))
      | r2_hidden(D_189,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_6])).

tff(c_1090,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_890,c_1070])).

tff(c_159,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_168,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_92,c_159])).

tff(c_391,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden('#skF_5'(A_132,B_133,C_134),B_133)
      | ~ r2_hidden(A_132,k9_relat_1(C_134,B_133))
      | ~ v1_relat_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_88,plain,(
    ! [F_53] :
      ( k1_funct_1('#skF_9',F_53) != '#skF_10'
      | ~ r2_hidden(F_53,'#skF_8')
      | ~ m1_subset_1(F_53,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_430,plain,(
    ! [A_132,C_134] :
      ( k1_funct_1('#skF_9','#skF_5'(A_132,'#skF_8',C_134)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'(A_132,'#skF_8',C_134),'#skF_6')
      | ~ r2_hidden(A_132,k9_relat_1(C_134,'#skF_8'))
      | ~ v1_relat_1(C_134) ) ),
    inference(resolution,[status(thm)],[c_391,c_88])).

tff(c_904,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_10','#skF_8','#skF_9'),'#skF_6')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_890,c_430])).

tff(c_913,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_10','#skF_8','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_904])).

tff(c_937,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_8','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_913])).

tff(c_94,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_294,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_relset_1(A_117,B_118,C_119) = k1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_303,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_92,c_294])).

tff(c_2575,plain,(
    ! [B_305,A_306,C_307] :
      ( k1_xboole_0 = B_305
      | k1_relset_1(A_306,B_305,C_307) = A_306
      | ~ v1_funct_2(C_307,A_306,B_305)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_306,B_305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2602,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_2575])).

tff(c_2611,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_303,c_2602])).

tff(c_2612,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2611])).

tff(c_1111,plain,(
    ! [A_193,B_194,C_195] :
      ( r2_hidden('#skF_5'(A_193,B_194,C_195),k1_relat_1(C_195))
      | ~ r2_hidden(A_193,k9_relat_1(C_195,B_194))
      | ~ v1_relat_1(C_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_50,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1115,plain,(
    ! [A_193,B_194,C_195] :
      ( m1_subset_1('#skF_5'(A_193,B_194,C_195),k1_relat_1(C_195))
      | ~ r2_hidden(A_193,k9_relat_1(C_195,B_194))
      | ~ v1_relat_1(C_195) ) ),
    inference(resolution,[status(thm)],[c_1111,c_50])).

tff(c_2617,plain,(
    ! [A_193,B_194] :
      ( m1_subset_1('#skF_5'(A_193,B_194,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_193,k9_relat_1('#skF_9',B_194))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2612,c_1115])).

tff(c_2632,plain,(
    ! [A_308,B_309] :
      ( m1_subset_1('#skF_5'(A_308,B_309,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_308,k9_relat_1('#skF_9',B_309)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_2617])).

tff(c_2651,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_8','#skF_9'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_890,c_2632])).

tff(c_2671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_937,c_2651])).

tff(c_2672,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2611])).

tff(c_34,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_246,plain,(
    ! [A_103,C_104,B_105] :
      ( ~ r2_hidden(A_103,C_104)
      | ~ r2_hidden(A_103,B_105)
      | ~ r2_hidden(A_103,k5_xboole_0(B_105,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_259,plain,(
    ! [A_103,A_12] :
      ( ~ r2_hidden(A_103,k1_xboole_0)
      | ~ r2_hidden(A_103,A_12)
      | ~ r2_hidden(A_103,A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_246])).

tff(c_2842,plain,(
    ! [A_317,A_318] :
      ( ~ r2_hidden(A_317,'#skF_7')
      | ~ r2_hidden(A_317,A_318)
      | ~ r2_hidden(A_317,A_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2672,c_259])).

tff(c_2871,plain,(
    ! [A_318] : ~ r2_hidden('#skF_10',A_318) ),
    inference(resolution,[status(thm)],[c_1090,c_2842])).

tff(c_2878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2871,c_1090])).

tff(c_2879,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_96,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3712,plain,(
    ! [A_391,B_392,C_393] :
      ( r2_hidden(k4_tarski('#skF_5'(A_391,B_392,C_393),A_391),C_393)
      | ~ r2_hidden(A_391,k9_relat_1(C_393,B_392))
      | ~ v1_relat_1(C_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_64,plain,(
    ! [C_31,A_29,B_30] :
      ( k1_funct_1(C_31,A_29) = B_30
      | ~ r2_hidden(k4_tarski(A_29,B_30),C_31)
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4611,plain,(
    ! [C_465,A_466,B_467] :
      ( k1_funct_1(C_465,'#skF_5'(A_466,B_467,C_465)) = A_466
      | ~ v1_funct_1(C_465)
      | ~ r2_hidden(A_466,k9_relat_1(C_465,B_467))
      | ~ v1_relat_1(C_465) ) ),
    inference(resolution,[status(thm)],[c_3712,c_64])).

tff(c_4625,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) = '#skF_10'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_890,c_4611])).

tff(c_4641,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_96,c_4625])).

tff(c_4643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2879,c_4641])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.72/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.72/2.12  
% 5.72/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.12  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 5.82/2.12  
% 5.82/2.12  %Foreground sorts:
% 5.82/2.12  
% 5.82/2.12  
% 5.82/2.12  %Background operators:
% 5.82/2.12  
% 5.82/2.12  
% 5.82/2.12  %Foreground operators:
% 5.82/2.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.82/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.82/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.82/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.82/2.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.82/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.82/2.12  tff('#skF_7', type, '#skF_7': $i).
% 5.82/2.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.82/2.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.82/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.82/2.12  tff('#skF_10', type, '#skF_10': $i).
% 5.82/2.12  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.82/2.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.82/2.12  tff('#skF_6', type, '#skF_6': $i).
% 5.82/2.12  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.82/2.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.82/2.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.82/2.12  tff('#skF_9', type, '#skF_9': $i).
% 5.82/2.12  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.82/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.82/2.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.82/2.12  tff('#skF_8', type, '#skF_8': $i).
% 5.82/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.82/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.82/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.82/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.82/2.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.82/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.82/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.82/2.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.82/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.82/2.12  
% 5.89/2.14  tff(f_141, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 5.89/2.14  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.89/2.14  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 5.89/2.14  tff(f_57, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.89/2.14  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.89/2.14  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.89/2.14  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.89/2.14  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.89/2.14  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.89/2.14  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 5.89/2.14  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.89/2.14  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.89/2.14  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.89/2.14  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.89/2.14  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.89/2.14  tff(f_88, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 5.89/2.14  tff(c_92, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.89/2.14  tff(c_877, plain, (![A_167, B_168, C_169, D_170]: (k7_relset_1(A_167, B_168, C_169, D_170)=k9_relat_1(C_169, D_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.89/2.14  tff(c_888, plain, (![D_170]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_170)=k9_relat_1('#skF_9', D_170))), inference(resolution, [status(thm)], [c_92, c_877])).
% 5.89/2.14  tff(c_90, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.89/2.14  tff(c_890, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_90])).
% 5.89/2.14  tff(c_963, plain, (![A_178, B_179, C_180, D_181]: (m1_subset_1(k7_relset_1(A_178, B_179, C_180, D_181), k1_zfmisc_1(B_179)) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.89/2.14  tff(c_984, plain, (![D_170]: (m1_subset_1(k9_relat_1('#skF_9', D_170), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_888, c_963])).
% 5.89/2.14  tff(c_992, plain, (![D_182]: (m1_subset_1(k9_relat_1('#skF_9', D_182), k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_984])).
% 5.89/2.14  tff(c_48, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.89/2.14  tff(c_129, plain, (![A_69, B_70]: (r2_hidden(A_69, B_70) | v1_xboole_0(B_70) | ~m1_subset_1(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.89/2.14  tff(c_36, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.89/2.14  tff(c_133, plain, (![A_69, A_13]: (r1_tarski(A_69, A_13) | v1_xboole_0(k1_zfmisc_1(A_13)) | ~m1_subset_1(A_69, k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_129, c_36])).
% 5.89/2.14  tff(c_139, plain, (![A_69, A_13]: (r1_tarski(A_69, A_13) | ~m1_subset_1(A_69, k1_zfmisc_1(A_13)))), inference(negUnitSimplification, [status(thm)], [c_48, c_133])).
% 5.89/2.14  tff(c_997, plain, (![D_183]: (r1_tarski(k9_relat_1('#skF_9', D_183), '#skF_7'))), inference(resolution, [status(thm)], [c_992, c_139])).
% 5.89/2.14  tff(c_32, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.89/2.14  tff(c_1002, plain, (![D_184]: (k2_xboole_0(k9_relat_1('#skF_9', D_184), '#skF_7')='#skF_7')), inference(resolution, [status(thm)], [c_997, c_32])).
% 5.89/2.14  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.89/2.14  tff(c_1070, plain, (![D_189, D_190]: (~r2_hidden(D_189, k9_relat_1('#skF_9', D_190)) | r2_hidden(D_189, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_6])).
% 5.89/2.14  tff(c_1090, plain, (r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_890, c_1070])).
% 5.89/2.14  tff(c_159, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.89/2.14  tff(c_168, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_92, c_159])).
% 5.89/2.14  tff(c_391, plain, (![A_132, B_133, C_134]: (r2_hidden('#skF_5'(A_132, B_133, C_134), B_133) | ~r2_hidden(A_132, k9_relat_1(C_134, B_133)) | ~v1_relat_1(C_134))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.89/2.14  tff(c_88, plain, (![F_53]: (k1_funct_1('#skF_9', F_53)!='#skF_10' | ~r2_hidden(F_53, '#skF_8') | ~m1_subset_1(F_53, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.89/2.14  tff(c_430, plain, (![A_132, C_134]: (k1_funct_1('#skF_9', '#skF_5'(A_132, '#skF_8', C_134))!='#skF_10' | ~m1_subset_1('#skF_5'(A_132, '#skF_8', C_134), '#skF_6') | ~r2_hidden(A_132, k9_relat_1(C_134, '#skF_8')) | ~v1_relat_1(C_134))), inference(resolution, [status(thm)], [c_391, c_88])).
% 5.89/2.14  tff(c_904, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_10', '#skF_8', '#skF_9'), '#skF_6') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_890, c_430])).
% 5.89/2.14  tff(c_913, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_10', '#skF_8', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_904])).
% 5.89/2.14  tff(c_937, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_8', '#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_913])).
% 5.89/2.14  tff(c_94, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.89/2.14  tff(c_294, plain, (![A_117, B_118, C_119]: (k1_relset_1(A_117, B_118, C_119)=k1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.89/2.14  tff(c_303, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_92, c_294])).
% 5.89/2.14  tff(c_2575, plain, (![B_305, A_306, C_307]: (k1_xboole_0=B_305 | k1_relset_1(A_306, B_305, C_307)=A_306 | ~v1_funct_2(C_307, A_306, B_305) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_306, B_305))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.89/2.14  tff(c_2602, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_92, c_2575])).
% 5.89/2.14  tff(c_2611, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_303, c_2602])).
% 5.89/2.14  tff(c_2612, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_2611])).
% 5.89/2.14  tff(c_1111, plain, (![A_193, B_194, C_195]: (r2_hidden('#skF_5'(A_193, B_194, C_195), k1_relat_1(C_195)) | ~r2_hidden(A_193, k9_relat_1(C_195, B_194)) | ~v1_relat_1(C_195))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.89/2.14  tff(c_50, plain, (![A_19, B_20]: (m1_subset_1(A_19, B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.89/2.14  tff(c_1115, plain, (![A_193, B_194, C_195]: (m1_subset_1('#skF_5'(A_193, B_194, C_195), k1_relat_1(C_195)) | ~r2_hidden(A_193, k9_relat_1(C_195, B_194)) | ~v1_relat_1(C_195))), inference(resolution, [status(thm)], [c_1111, c_50])).
% 5.89/2.14  tff(c_2617, plain, (![A_193, B_194]: (m1_subset_1('#skF_5'(A_193, B_194, '#skF_9'), '#skF_6') | ~r2_hidden(A_193, k9_relat_1('#skF_9', B_194)) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2612, c_1115])).
% 5.89/2.14  tff(c_2632, plain, (![A_308, B_309]: (m1_subset_1('#skF_5'(A_308, B_309, '#skF_9'), '#skF_6') | ~r2_hidden(A_308, k9_relat_1('#skF_9', B_309)))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_2617])).
% 5.89/2.14  tff(c_2651, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_8', '#skF_9'), '#skF_6')), inference(resolution, [status(thm)], [c_890, c_2632])).
% 5.89/2.14  tff(c_2671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_937, c_2651])).
% 5.89/2.14  tff(c_2672, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2611])).
% 5.89/2.14  tff(c_34, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.89/2.14  tff(c_246, plain, (![A_103, C_104, B_105]: (~r2_hidden(A_103, C_104) | ~r2_hidden(A_103, B_105) | ~r2_hidden(A_103, k5_xboole_0(B_105, C_104)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.89/2.14  tff(c_259, plain, (![A_103, A_12]: (~r2_hidden(A_103, k1_xboole_0) | ~r2_hidden(A_103, A_12) | ~r2_hidden(A_103, A_12))), inference(superposition, [status(thm), theory('equality')], [c_34, c_246])).
% 5.89/2.14  tff(c_2842, plain, (![A_317, A_318]: (~r2_hidden(A_317, '#skF_7') | ~r2_hidden(A_317, A_318) | ~r2_hidden(A_317, A_318))), inference(demodulation, [status(thm), theory('equality')], [c_2672, c_259])).
% 5.89/2.14  tff(c_2871, plain, (![A_318]: (~r2_hidden('#skF_10', A_318))), inference(resolution, [status(thm)], [c_1090, c_2842])).
% 5.89/2.14  tff(c_2878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2871, c_1090])).
% 5.89/2.14  tff(c_2879, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10'), inference(splitRight, [status(thm)], [c_913])).
% 5.89/2.14  tff(c_96, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.89/2.14  tff(c_3712, plain, (![A_391, B_392, C_393]: (r2_hidden(k4_tarski('#skF_5'(A_391, B_392, C_393), A_391), C_393) | ~r2_hidden(A_391, k9_relat_1(C_393, B_392)) | ~v1_relat_1(C_393))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.89/2.14  tff(c_64, plain, (![C_31, A_29, B_30]: (k1_funct_1(C_31, A_29)=B_30 | ~r2_hidden(k4_tarski(A_29, B_30), C_31) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.89/2.14  tff(c_4611, plain, (![C_465, A_466, B_467]: (k1_funct_1(C_465, '#skF_5'(A_466, B_467, C_465))=A_466 | ~v1_funct_1(C_465) | ~r2_hidden(A_466, k9_relat_1(C_465, B_467)) | ~v1_relat_1(C_465))), inference(resolution, [status(thm)], [c_3712, c_64])).
% 5.89/2.14  tff(c_4625, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))='#skF_10' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_890, c_4611])).
% 5.89/2.14  tff(c_4641, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_96, c_4625])).
% 5.89/2.14  tff(c_4643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2879, c_4641])).
% 5.89/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.14  
% 5.89/2.14  Inference rules
% 5.89/2.14  ----------------------
% 5.89/2.14  #Ref     : 0
% 5.89/2.14  #Sup     : 963
% 5.89/2.14  #Fact    : 0
% 5.89/2.14  #Define  : 0
% 5.89/2.14  #Split   : 10
% 5.89/2.14  #Chain   : 0
% 5.89/2.14  #Close   : 0
% 5.89/2.14  
% 5.89/2.14  Ordering : KBO
% 5.89/2.14  
% 5.89/2.14  Simplification rules
% 5.89/2.14  ----------------------
% 5.89/2.14  #Subsume      : 132
% 5.89/2.14  #Demod        : 134
% 5.89/2.14  #Tautology    : 141
% 5.89/2.14  #SimpNegUnit  : 13
% 5.89/2.14  #BackRed      : 33
% 5.89/2.14  
% 5.89/2.14  #Partial instantiations: 0
% 5.89/2.14  #Strategies tried      : 1
% 5.89/2.14  
% 5.89/2.14  Timing (in seconds)
% 5.89/2.14  ----------------------
% 5.89/2.14  Preprocessing        : 0.35
% 5.89/2.14  Parsing              : 0.18
% 5.89/2.14  CNF conversion       : 0.03
% 5.89/2.14  Main loop            : 0.99
% 5.89/2.14  Inferencing          : 0.36
% 5.89/2.14  Reduction            : 0.27
% 5.89/2.14  Demodulation         : 0.17
% 5.89/2.14  BG Simplification    : 0.05
% 5.89/2.14  Subsumption          : 0.21
% 5.89/2.14  Abstraction          : 0.07
% 5.89/2.14  MUC search           : 0.00
% 5.89/2.14  Cooper               : 0.00
% 5.89/2.14  Total                : 1.38
% 5.89/2.14  Index Insertion      : 0.00
% 5.89/2.14  Index Deletion       : 0.00
% 5.89/2.14  Index Matching       : 0.00
% 5.89/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
