%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:44 EST 2020

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :  139 (3483 expanded)
%              Number of leaves         :   46 (1261 expanded)
%              Depth                    :   16
%              Number of atoms          :  216 (11139 expanded)
%              Number of equality atoms :   71 (3529 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_126,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => v1_funct_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_grfunc_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_76,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68])).

tff(c_70,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_667,plain,(
    ! [B_146,C_147,A_148] :
      ( k1_xboole_0 = B_146
      | v1_funct_2(C_147,A_148,B_146)
      | k1_relset_1(A_148,B_146,C_147) != A_148
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_680,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_6','#skF_4','#skF_5')
    | k1_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_72,c_667])).

tff(c_694,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_680])).

tff(c_695,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_694])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_1'(A_8,B_9),B_9)
      | k1_xboole_0 = B_9
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_714,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_1'(A_8,B_9),B_9)
      | B_9 = '#skF_5'
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_14])).

tff(c_403,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_410,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_403])).

tff(c_419,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_410])).

tff(c_8,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_728,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_695,c_8])).

tff(c_819,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_72])).

tff(c_10,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_413,plain,(
    ! [B_5,C_93] :
      ( k1_relset_1(k1_xboole_0,B_5,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_403])).

tff(c_1049,plain,(
    ! [B_181,C_182] :
      ( k1_relset_1('#skF_5',B_181,C_182) = k1_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_695,c_413])).

tff(c_1051,plain,(
    ! [B_181] : k1_relset_1('#skF_5',B_181,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_819,c_1049])).

tff(c_1055,plain,(
    ! [B_181] : k1_relset_1('#skF_5',B_181,'#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_1051])).

tff(c_52,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_78,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_1173,plain,(
    ! [C_199,B_200] :
      ( v1_funct_2(C_199,'#skF_5',B_200)
      | k1_relset_1('#skF_5',B_200,C_199) != '#skF_5'
      | ~ m1_subset_1(C_199,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_695,c_695,c_695,c_78])).

tff(c_1178,plain,(
    ! [B_200] :
      ( v1_funct_2('#skF_6','#skF_5',B_200)
      | k1_relset_1('#skF_5',B_200,'#skF_6') != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_819,c_1173])).

tff(c_1183,plain,(
    ! [B_200] :
      ( v1_funct_2('#skF_6','#skF_5',B_200)
      | '#skF_5' != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1178])).

tff(c_1188,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1183])).

tff(c_186,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_194,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_186])).

tff(c_32,plain,(
    ! [A_18,C_20] :
      ( r2_hidden(k4_tarski(A_18,k1_funct_1(C_20,A_18)),C_20)
      | ~ r2_hidden(A_18,k1_relat_1(C_20))
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    ! [A_11] :
      ( k7_relat_1(A_11,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_209,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_194,c_18])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_214,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_28])).

tff(c_221,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_74,c_214])).

tff(c_721,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_221])).

tff(c_160,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_168,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_160])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [A_46,B_47] :
      ( v1_funct_1(k3_xboole_0(A_46,B_47))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_134,plain,(
    ! [A_1] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_135,plain,(
    ! [A_1] :
      ( ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_171,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_168,c_135])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_171])).

tff(c_179,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_724,plain,(
    v1_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_179])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_732,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_695,c_24])).

tff(c_20,plain,(
    ! [A_12] : k9_relat_1(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_729,plain,(
    ! [A_12] : k9_relat_1('#skF_5',A_12) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_695,c_20])).

tff(c_838,plain,(
    ! [C_159,A_160,B_161] :
      ( k2_tarski(k1_funct_1(C_159,A_160),k1_funct_1(C_159,B_161)) = k9_relat_1(C_159,k2_tarski(A_160,B_161))
      | ~ r2_hidden(B_161,k1_relat_1(C_159))
      | ~ r2_hidden(A_160,k1_relat_1(C_159))
      | ~ v1_funct_1(C_159)
      | ~ v1_relat_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_195,plain,(
    ! [A_65,B_66] : k2_xboole_0(k1_tarski(A_65),k1_tarski(B_66)) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),B_7) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_200,plain,(
    ! [A_65,B_66] : k2_tarski(A_65,B_66) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_12])).

tff(c_723,plain,(
    ! [A_65,B_66] : k2_tarski(A_65,B_66) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_200])).

tff(c_1493,plain,(
    ! [C_256,A_257,B_258] :
      ( k9_relat_1(C_256,k2_tarski(A_257,B_258)) != '#skF_5'
      | ~ r2_hidden(B_258,k1_relat_1(C_256))
      | ~ r2_hidden(A_257,k1_relat_1(C_256))
      | ~ v1_funct_1(C_256)
      | ~ v1_relat_1(C_256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_723])).

tff(c_1504,plain,(
    ! [B_258,A_257] :
      ( ~ r2_hidden(B_258,k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_257,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_1493])).

tff(c_1509,plain,(
    ! [B_258,A_257] :
      ( ~ r2_hidden(B_258,'#skF_5')
      | ~ r2_hidden(A_257,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_724,c_732,c_732,c_1504])).

tff(c_1510,plain,(
    ! [A_257] : ~ r2_hidden(A_257,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1509])).

tff(c_603,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( r2_hidden('#skF_3'(A_128,B_129,C_130,D_131),C_130)
      | ~ r2_hidden(A_128,D_131)
      | ~ m1_subset_1(D_131,k1_zfmisc_1(k2_zfmisc_1(B_129,C_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_620,plain,(
    ! [A_128] :
      ( r2_hidden('#skF_3'(A_128,'#skF_4','#skF_5','#skF_6'),'#skF_5')
      | ~ r2_hidden(A_128,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_603])).

tff(c_1545,plain,(
    ! [A_260] : ~ r2_hidden(A_260,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1510,c_620])).

tff(c_1559,plain,(
    ! [A_18] :
      ( ~ r2_hidden(A_18,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_1545])).

tff(c_1566,plain,(
    ! [A_261] : ~ r2_hidden(A_261,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_74,c_419,c_1559])).

tff(c_1576,plain,(
    ! [A_8] :
      ( '#skF_5' = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_714,c_1566])).

tff(c_1585,plain,(
    ! [A_8] : ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(negUnitSimplification,[status(thm)],[c_1188,c_1576])).

tff(c_1562,plain,(
    ! [A_8] :
      ( '#skF_5' = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_714,c_1545])).

tff(c_1594,plain,(
    ! [A_8] : ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ),
    inference(splitLeft,[status(thm)],[c_1562])).

tff(c_1610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1594,c_819])).

tff(c_1611,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1562])).

tff(c_1650,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_1611,c_732])).

tff(c_1655,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_1650])).

tff(c_429,plain,(
    ! [A_94] :
      ( m1_subset_1(A_94,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_94),k2_relat_1(A_94))))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_438,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1('#skF_6'))))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_429])).

tff(c_448,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_74,c_438])).

tff(c_1665,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1655,c_1655,c_448])).

tff(c_1671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1585,c_1665])).

tff(c_1672,plain,(
    ! [B_258] : ~ r2_hidden(B_258,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1509])).

tff(c_1753,plain,(
    ! [A_268] : ~ r2_hidden(A_268,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1672,c_620])).

tff(c_1770,plain,(
    ! [A_8] :
      ( '#skF_5' = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_714,c_1753])).

tff(c_1815,plain,(
    ! [A_8] : ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ),
    inference(splitLeft,[status(thm)],[c_1770])).

tff(c_1818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1815,c_819])).

tff(c_1819,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1770])).

tff(c_1827,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1819,c_1188])).

tff(c_1857,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1819,c_1819,c_732])).

tff(c_1862,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_1857])).

tff(c_1869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1827,c_1862])).

tff(c_1871,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1183])).

tff(c_1870,plain,(
    ! [B_200] : v1_funct_2('#skF_6','#skF_5',B_200) ),
    inference(splitRight,[status(thm)],[c_1183])).

tff(c_2008,plain,(
    ! [B_200] : v1_funct_2('#skF_6','#skF_4',B_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1871,c_1870])).

tff(c_1913,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1871,c_76])).

tff(c_2012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_1913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:56:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.82  
% 4.39/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.83  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.39/1.83  
% 4.39/1.83  %Foreground sorts:
% 4.39/1.83  
% 4.39/1.83  
% 4.39/1.83  %Background operators:
% 4.39/1.83  
% 4.39/1.83  
% 4.39/1.83  %Foreground operators:
% 4.39/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.39/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.39/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.39/1.83  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.39/1.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.39/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.39/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.39/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.39/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.39/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.39/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.39/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.39/1.83  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.39/1.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.39/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.39/1.83  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.39/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.39/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.39/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.39/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.39/1.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.39/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.39/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.39/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.39/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.39/1.83  
% 4.39/1.86  tff(f_155, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 4.39/1.86  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.39/1.86  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.39/1.86  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.39/1.86  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.39/1.86  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.39/1.86  tff(f_87, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.39/1.86  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 4.39/1.86  tff(f_67, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 4.39/1.86  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.39/1.86  tff(f_132, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => v1_funct_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_grfunc_1)).
% 4.39/1.86  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.39/1.86  tff(f_56, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 4.39/1.86  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 4.39/1.86  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 4.39/1.86  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.39/1.86  tff(f_108, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 4.39/1.86  tff(f_142, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.39/1.86  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.39/1.86  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.39/1.86  tff(c_68, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.39/1.86  tff(c_76, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68])).
% 4.39/1.86  tff(c_70, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.39/1.86  tff(c_667, plain, (![B_146, C_147, A_148]: (k1_xboole_0=B_146 | v1_funct_2(C_147, A_148, B_146) | k1_relset_1(A_148, B_146, C_147)!=A_148 | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_146))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.39/1.86  tff(c_680, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_4'), inference(resolution, [status(thm)], [c_72, c_667])).
% 4.39/1.86  tff(c_694, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_680])).
% 4.39/1.86  tff(c_695, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_76, c_694])).
% 4.39/1.86  tff(c_14, plain, (![A_8, B_9]: (r2_hidden('#skF_1'(A_8, B_9), B_9) | k1_xboole_0=B_9 | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.39/1.86  tff(c_714, plain, (![A_8, B_9]: (r2_hidden('#skF_1'(A_8, B_9), B_9) | B_9='#skF_5' | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_695, c_14])).
% 4.39/1.86  tff(c_403, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.39/1.86  tff(c_410, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_403])).
% 4.39/1.86  tff(c_419, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_410])).
% 4.39/1.86  tff(c_8, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.39/1.86  tff(c_728, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_695, c_8])).
% 4.39/1.86  tff(c_819, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_728, c_72])).
% 4.39/1.86  tff(c_10, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.39/1.86  tff(c_413, plain, (![B_5, C_93]: (k1_relset_1(k1_xboole_0, B_5, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_403])).
% 4.39/1.86  tff(c_1049, plain, (![B_181, C_182]: (k1_relset_1('#skF_5', B_181, C_182)=k1_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_695, c_695, c_413])).
% 4.39/1.86  tff(c_1051, plain, (![B_181]: (k1_relset_1('#skF_5', B_181, '#skF_6')=k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_819, c_1049])).
% 4.39/1.86  tff(c_1055, plain, (![B_181]: (k1_relset_1('#skF_5', B_181, '#skF_6')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_419, c_1051])).
% 4.39/1.86  tff(c_52, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.39/1.86  tff(c_78, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_52])).
% 4.39/1.86  tff(c_1173, plain, (![C_199, B_200]: (v1_funct_2(C_199, '#skF_5', B_200) | k1_relset_1('#skF_5', B_200, C_199)!='#skF_5' | ~m1_subset_1(C_199, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_695, c_695, c_695, c_695, c_78])).
% 4.39/1.86  tff(c_1178, plain, (![B_200]: (v1_funct_2('#skF_6', '#skF_5', B_200) | k1_relset_1('#skF_5', B_200, '#skF_6')!='#skF_5')), inference(resolution, [status(thm)], [c_819, c_1173])).
% 4.39/1.86  tff(c_1183, plain, (![B_200]: (v1_funct_2('#skF_6', '#skF_5', B_200) | '#skF_5'!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1178])).
% 4.39/1.86  tff(c_1188, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_1183])).
% 4.39/1.86  tff(c_186, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.39/1.86  tff(c_194, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_186])).
% 4.39/1.86  tff(c_32, plain, (![A_18, C_20]: (r2_hidden(k4_tarski(A_18, k1_funct_1(C_20, A_18)), C_20) | ~r2_hidden(A_18, k1_relat_1(C_20)) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.39/1.86  tff(c_18, plain, (![A_11]: (k7_relat_1(A_11, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.39/1.86  tff(c_209, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_194, c_18])).
% 4.39/1.86  tff(c_28, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.39/1.86  tff(c_214, plain, (v1_relat_1(k1_xboole_0) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_209, c_28])).
% 4.39/1.86  tff(c_221, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_74, c_214])).
% 4.39/1.86  tff(c_721, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_221])).
% 4.39/1.86  tff(c_160, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.39/1.86  tff(c_168, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_160])).
% 4.39/1.86  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.39/1.86  tff(c_131, plain, (![A_46, B_47]: (v1_funct_1(k3_xboole_0(A_46, B_47)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.39/1.86  tff(c_134, plain, (![A_1]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_131])).
% 4.39/1.86  tff(c_135, plain, (![A_1]: (~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_134])).
% 4.39/1.86  tff(c_171, plain, (~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_168, c_135])).
% 4.39/1.86  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_171])).
% 4.39/1.86  tff(c_179, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_134])).
% 4.39/1.86  tff(c_724, plain, (v1_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_179])).
% 4.39/1.86  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.39/1.86  tff(c_732, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_695, c_695, c_24])).
% 4.39/1.86  tff(c_20, plain, (![A_12]: (k9_relat_1(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.39/1.86  tff(c_729, plain, (![A_12]: (k9_relat_1('#skF_5', A_12)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_695, c_20])).
% 4.39/1.86  tff(c_838, plain, (![C_159, A_160, B_161]: (k2_tarski(k1_funct_1(C_159, A_160), k1_funct_1(C_159, B_161))=k9_relat_1(C_159, k2_tarski(A_160, B_161)) | ~r2_hidden(B_161, k1_relat_1(C_159)) | ~r2_hidden(A_160, k1_relat_1(C_159)) | ~v1_funct_1(C_159) | ~v1_relat_1(C_159))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.39/1.86  tff(c_195, plain, (![A_65, B_66]: (k2_xboole_0(k1_tarski(A_65), k1_tarski(B_66))=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.39/1.86  tff(c_12, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.39/1.86  tff(c_200, plain, (![A_65, B_66]: (k2_tarski(A_65, B_66)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_195, c_12])).
% 4.39/1.86  tff(c_723, plain, (![A_65, B_66]: (k2_tarski(A_65, B_66)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_200])).
% 4.39/1.86  tff(c_1493, plain, (![C_256, A_257, B_258]: (k9_relat_1(C_256, k2_tarski(A_257, B_258))!='#skF_5' | ~r2_hidden(B_258, k1_relat_1(C_256)) | ~r2_hidden(A_257, k1_relat_1(C_256)) | ~v1_funct_1(C_256) | ~v1_relat_1(C_256))), inference(superposition, [status(thm), theory('equality')], [c_838, c_723])).
% 4.39/1.86  tff(c_1504, plain, (![B_258, A_257]: (~r2_hidden(B_258, k1_relat_1('#skF_5')) | ~r2_hidden(A_257, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_729, c_1493])).
% 4.39/1.86  tff(c_1509, plain, (![B_258, A_257]: (~r2_hidden(B_258, '#skF_5') | ~r2_hidden(A_257, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_721, c_724, c_732, c_732, c_1504])).
% 4.39/1.86  tff(c_1510, plain, (![A_257]: (~r2_hidden(A_257, '#skF_5'))), inference(splitLeft, [status(thm)], [c_1509])).
% 4.39/1.86  tff(c_603, plain, (![A_128, B_129, C_130, D_131]: (r2_hidden('#skF_3'(A_128, B_129, C_130, D_131), C_130) | ~r2_hidden(A_128, D_131) | ~m1_subset_1(D_131, k1_zfmisc_1(k2_zfmisc_1(B_129, C_130))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.39/1.86  tff(c_620, plain, (![A_128]: (r2_hidden('#skF_3'(A_128, '#skF_4', '#skF_5', '#skF_6'), '#skF_5') | ~r2_hidden(A_128, '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_603])).
% 4.39/1.86  tff(c_1545, plain, (![A_260]: (~r2_hidden(A_260, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1510, c_620])).
% 4.39/1.86  tff(c_1559, plain, (![A_18]: (~r2_hidden(A_18, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_1545])).
% 4.39/1.86  tff(c_1566, plain, (![A_261]: (~r2_hidden(A_261, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_74, c_419, c_1559])).
% 4.39/1.86  tff(c_1576, plain, (![A_8]: ('#skF_5'='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_714, c_1566])).
% 4.39/1.86  tff(c_1585, plain, (![A_8]: (~m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(negUnitSimplification, [status(thm)], [c_1188, c_1576])).
% 4.39/1.86  tff(c_1562, plain, (![A_8]: ('#skF_5'='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_714, c_1545])).
% 4.39/1.86  tff(c_1594, plain, (![A_8]: (~m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(splitLeft, [status(thm)], [c_1562])).
% 4.39/1.86  tff(c_1610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1594, c_819])).
% 4.39/1.86  tff(c_1611, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1562])).
% 4.39/1.86  tff(c_1650, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_1611, c_732])).
% 4.39/1.86  tff(c_1655, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_1650])).
% 4.39/1.86  tff(c_429, plain, (![A_94]: (m1_subset_1(A_94, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_94), k2_relat_1(A_94)))) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.39/1.86  tff(c_438, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1('#skF_6')))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_419, c_429])).
% 4.39/1.86  tff(c_448, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_74, c_438])).
% 4.39/1.86  tff(c_1665, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1655, c_1655, c_448])).
% 4.39/1.86  tff(c_1671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1585, c_1665])).
% 4.39/1.86  tff(c_1672, plain, (![B_258]: (~r2_hidden(B_258, '#skF_5'))), inference(splitRight, [status(thm)], [c_1509])).
% 4.39/1.86  tff(c_1753, plain, (![A_268]: (~r2_hidden(A_268, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1672, c_620])).
% 4.39/1.86  tff(c_1770, plain, (![A_8]: ('#skF_5'='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_714, c_1753])).
% 4.39/1.86  tff(c_1815, plain, (![A_8]: (~m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(splitLeft, [status(thm)], [c_1770])).
% 4.39/1.86  tff(c_1818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1815, c_819])).
% 4.39/1.86  tff(c_1819, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1770])).
% 4.39/1.86  tff(c_1827, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1819, c_1188])).
% 4.39/1.86  tff(c_1857, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1819, c_1819, c_732])).
% 4.39/1.86  tff(c_1862, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_1857])).
% 4.39/1.86  tff(c_1869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1827, c_1862])).
% 4.39/1.86  tff(c_1871, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_1183])).
% 4.39/1.86  tff(c_1870, plain, (![B_200]: (v1_funct_2('#skF_6', '#skF_5', B_200))), inference(splitRight, [status(thm)], [c_1183])).
% 4.39/1.86  tff(c_2008, plain, (![B_200]: (v1_funct_2('#skF_6', '#skF_4', B_200))), inference(demodulation, [status(thm), theory('equality')], [c_1871, c_1870])).
% 4.39/1.86  tff(c_1913, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1871, c_76])).
% 4.39/1.86  tff(c_2012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2008, c_1913])).
% 4.39/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.86  
% 4.39/1.86  Inference rules
% 4.39/1.86  ----------------------
% 4.39/1.86  #Ref     : 0
% 4.39/1.86  #Sup     : 395
% 4.39/1.86  #Fact    : 0
% 4.39/1.86  #Define  : 0
% 4.39/1.86  #Split   : 9
% 4.39/1.86  #Chain   : 0
% 4.39/1.86  #Close   : 0
% 4.39/1.86  
% 4.39/1.86  Ordering : KBO
% 4.39/1.86  
% 4.39/1.86  Simplification rules
% 4.39/1.86  ----------------------
% 4.39/1.86  #Subsume      : 109
% 4.39/1.86  #Demod        : 682
% 4.39/1.86  #Tautology    : 202
% 4.39/1.86  #SimpNegUnit  : 26
% 4.39/1.86  #BackRed      : 184
% 4.39/1.86  
% 4.39/1.86  #Partial instantiations: 0
% 4.39/1.86  #Strategies tried      : 1
% 4.39/1.86  
% 4.39/1.86  Timing (in seconds)
% 4.39/1.86  ----------------------
% 4.39/1.87  Preprocessing        : 0.37
% 4.39/1.87  Parsing              : 0.20
% 4.39/1.87  CNF conversion       : 0.02
% 4.39/1.87  Main loop            : 0.60
% 4.39/1.87  Inferencing          : 0.21
% 4.39/1.87  Reduction            : 0.20
% 4.39/1.87  Demodulation         : 0.14
% 4.39/1.87  BG Simplification    : 0.03
% 4.39/1.87  Subsumption          : 0.11
% 4.39/1.87  Abstraction          : 0.03
% 4.39/1.87  MUC search           : 0.00
% 4.39/1.87  Cooper               : 0.00
% 4.39/1.87  Total                : 1.05
% 4.39/1.87  Index Insertion      : 0.00
% 4.39/1.87  Index Deletion       : 0.00
% 4.39/1.87  Index Matching       : 0.00
% 4.39/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
