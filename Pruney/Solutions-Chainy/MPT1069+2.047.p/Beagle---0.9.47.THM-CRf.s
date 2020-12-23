%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:51 EST 2020

% Result     : Theorem 22.54s
% Output     : CNFRefutation 22.54s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 278 expanded)
%              Number of leaves         :   48 ( 118 expanded)
%              Depth                    :   12
%              Number of atoms          :  228 ( 890 expanded)
%              Number of equality atoms :   61 ( 206 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_143,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_108,axiom,(
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

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_62,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_70,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_427,plain,(
    ! [A_141,B_142,C_143] :
      ( k2_relset_1(A_141,B_142,C_143) = k2_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_444,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_427])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_358,plain,(
    ! [A_136,B_137,C_138] :
      ( k1_relset_1(A_136,B_137,C_138) = k1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_376,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_358])).

tff(c_60,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_381,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_60])).

tff(c_450,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_381])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_66,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1189,plain,(
    ! [E_216,C_217,D_221,B_220,F_218,A_219] :
      ( k1_funct_1(k8_funct_2(B_220,C_217,A_219,D_221,E_216),F_218) = k1_funct_1(E_216,k1_funct_1(D_221,F_218))
      | k1_xboole_0 = B_220
      | ~ r1_tarski(k2_relset_1(B_220,C_217,D_221),k1_relset_1(C_217,A_219,E_216))
      | ~ m1_subset_1(F_218,B_220)
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(C_217,A_219)))
      | ~ v1_funct_1(E_216)
      | ~ m1_subset_1(D_221,k1_zfmisc_1(k2_zfmisc_1(B_220,C_217)))
      | ~ v1_funct_2(D_221,B_220,C_217)
      | ~ v1_funct_1(D_221)
      | v1_xboole_0(C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1201,plain,(
    ! [B_220,D_221,F_218] :
      ( k1_funct_1(k8_funct_2(B_220,'#skF_5','#skF_3',D_221,'#skF_7'),F_218) = k1_funct_1('#skF_7',k1_funct_1(D_221,F_218))
      | k1_xboole_0 = B_220
      | ~ r1_tarski(k2_relset_1(B_220,'#skF_5',D_221),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_218,B_220)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_221,k1_zfmisc_1(k2_zfmisc_1(B_220,'#skF_5')))
      | ~ v1_funct_2(D_221,B_220,'#skF_5')
      | ~ v1_funct_1(D_221)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_1189])).

tff(c_1218,plain,(
    ! [B_220,D_221,F_218] :
      ( k1_funct_1(k8_funct_2(B_220,'#skF_5','#skF_3',D_221,'#skF_7'),F_218) = k1_funct_1('#skF_7',k1_funct_1(D_221,F_218))
      | k1_xboole_0 = B_220
      | ~ r1_tarski(k2_relset_1(B_220,'#skF_5',D_221),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_218,B_220)
      | ~ m1_subset_1(D_221,k1_zfmisc_1(k2_zfmisc_1(B_220,'#skF_5')))
      | ~ v1_funct_2(D_221,B_220,'#skF_5')
      | ~ v1_funct_1(D_221)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1201])).

tff(c_1471,plain,(
    ! [B_244,D_245,F_246] :
      ( k1_funct_1(k8_funct_2(B_244,'#skF_5','#skF_3',D_245,'#skF_7'),F_246) = k1_funct_1('#skF_7',k1_funct_1(D_245,F_246))
      | k1_xboole_0 = B_244
      | ~ r1_tarski(k2_relset_1(B_244,'#skF_5',D_245),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_246,B_244)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(B_244,'#skF_5')))
      | ~ v1_funct_2(D_245,B_244,'#skF_5')
      | ~ v1_funct_1(D_245) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1218])).

tff(c_1479,plain,(
    ! [F_246] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_246) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_246))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_246,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_1471])).

tff(c_1487,plain,(
    ! [F_246] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_246) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_246))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_246,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_450,c_1479])).

tff(c_1488,plain,(
    ! [F_246] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_246) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_246))
      | ~ m1_subset_1(F_246,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1487])).

tff(c_290,plain,(
    ! [B_126,A_127] :
      ( m1_subset_1(k1_tarski(B_126),k1_zfmisc_1(A_127))
      | k1_xboole_0 = A_127
      | ~ m1_subset_1(B_126,A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_495,plain,(
    ! [B_146,A_147] :
      ( r1_tarski(k1_tarski(B_146),A_147)
      | k1_xboole_0 = A_147
      | ~ m1_subset_1(B_146,A_147) ) ),
    inference(resolution,[status(thm)],[c_290,c_22])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | ~ r1_tarski(k1_tarski(A_10),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_516,plain,(
    ! [B_146,A_147] :
      ( r2_hidden(B_146,A_147)
      | k1_xboole_0 = A_147
      | ~ m1_subset_1(B_146,A_147) ) ),
    inference(resolution,[status(thm)],[c_495,c_12])).

tff(c_145,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_158,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_145])).

tff(c_445,plain,(
    k2_relset_1('#skF_5','#skF_3','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_427])).

tff(c_544,plain,(
    ! [A_150,B_151,C_152] :
      ( m1_subset_1(k2_relset_1(A_150,B_151,C_152),k1_zfmisc_1(B_151))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_565,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_544])).

tff(c_575,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_565])).

tff(c_585,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_575,c_22])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( v5_relat_1(B_21,A_20)
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_594,plain,
    ( v5_relat_1('#skF_7','#skF_3')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_585,c_26])).

tff(c_599,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_594])).

tff(c_157,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_145])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_90,B_91] :
      ( k2_xboole_0(k1_tarski(A_90),B_91) = B_91
      | ~ r2_hidden(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),B_15) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126,plain,(
    ! [B_92,A_93] :
      ( k1_xboole_0 != B_92
      | ~ r2_hidden(A_93,B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_18])).

tff(c_136,plain,(
    ! [A_94] :
      ( k1_xboole_0 != A_94
      | v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_144,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_136,c_74])).

tff(c_375,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_358])).

tff(c_960,plain,(
    ! [B_194,A_195,C_196] :
      ( k1_xboole_0 = B_194
      | k1_relset_1(A_195,B_194,C_196) = A_195
      | ~ v1_funct_2(C_196,A_195,B_194)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_975,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_960])).

tff(c_984,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_375,c_975])).

tff(c_985,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_984])).

tff(c_624,plain,(
    ! [B_153,A_154] :
      ( r2_hidden(k1_funct_1(B_153,A_154),k2_relat_1(B_153))
      | ~ r2_hidden(A_154,k1_relat_1(B_153))
      | ~ v1_funct_1(B_153)
      | ~ v1_relat_1(B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9926,plain,(
    ! [B_953,A_954,B_955] :
      ( r2_hidden(k1_funct_1(B_953,A_954),B_955)
      | ~ r1_tarski(k2_relat_1(B_953),B_955)
      | ~ r2_hidden(A_954,k1_relat_1(B_953))
      | ~ v1_funct_1(B_953)
      | ~ v1_relat_1(B_953) ) ),
    inference(resolution,[status(thm)],[c_624,c_6])).

tff(c_52,plain,(
    ! [A_39,B_40,C_42] :
      ( k7_partfun1(A_39,B_40,C_42) = k1_funct_1(B_40,C_42)
      | ~ r2_hidden(C_42,k1_relat_1(B_40))
      | ~ v1_funct_1(B_40)
      | ~ v5_relat_1(B_40,A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_27005,plain,(
    ! [A_1755,B_1756,B_1757,A_1758] :
      ( k7_partfun1(A_1755,B_1756,k1_funct_1(B_1757,A_1758)) = k1_funct_1(B_1756,k1_funct_1(B_1757,A_1758))
      | ~ v1_funct_1(B_1756)
      | ~ v5_relat_1(B_1756,A_1755)
      | ~ v1_relat_1(B_1756)
      | ~ r1_tarski(k2_relat_1(B_1757),k1_relat_1(B_1756))
      | ~ r2_hidden(A_1758,k1_relat_1(B_1757))
      | ~ v1_funct_1(B_1757)
      | ~ v1_relat_1(B_1757) ) ),
    inference(resolution,[status(thm)],[c_9926,c_52])).

tff(c_27028,plain,(
    ! [A_1755,A_1758] :
      ( k7_partfun1(A_1755,'#skF_7',k1_funct_1('#skF_6',A_1758)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_1758))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_1755)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_1758,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_450,c_27005])).

tff(c_48231,plain,(
    ! [A_2405,A_2406] :
      ( k7_partfun1(A_2405,'#skF_7',k1_funct_1('#skF_6',A_2406)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_2406))
      | ~ v5_relat_1('#skF_7',A_2405)
      | ~ r2_hidden(A_2406,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_72,c_985,c_158,c_66,c_27028])).

tff(c_56,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_48237,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48231,c_56])).

tff(c_48243,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_48237])).

tff(c_48387,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48243])).

tff(c_48390,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_516,c_48387])).

tff(c_48393,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_48390])).

tff(c_48395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_48393])).

tff(c_48396,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_48243])).

tff(c_52303,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_48396])).

tff(c_52310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.54/13.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.54/13.91  
% 22.54/13.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.54/13.92  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 22.54/13.92  
% 22.54/13.92  %Foreground sorts:
% 22.54/13.92  
% 22.54/13.92  
% 22.54/13.92  %Background operators:
% 22.54/13.92  
% 22.54/13.92  
% 22.54/13.92  %Foreground operators:
% 22.54/13.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 22.54/13.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.54/13.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.54/13.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.54/13.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.54/13.92  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.54/13.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.54/13.92  tff('#skF_7', type, '#skF_7': $i).
% 22.54/13.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.54/13.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 22.54/13.92  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 22.54/13.92  tff('#skF_5', type, '#skF_5': $i).
% 22.54/13.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.54/13.92  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 22.54/13.92  tff('#skF_6', type, '#skF_6': $i).
% 22.54/13.92  tff('#skF_3', type, '#skF_3': $i).
% 22.54/13.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 22.54/13.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 22.54/13.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.54/13.92  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 22.54/13.92  tff('#skF_8', type, '#skF_8': $i).
% 22.54/13.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.54/13.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.54/13.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.54/13.92  tff('#skF_4', type, '#skF_4': $i).
% 22.54/13.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.54/13.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.54/13.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.54/13.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.54/13.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.54/13.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.54/13.92  
% 22.54/13.94  tff(f_168, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 22.54/13.94  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 22.54/13.94  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 22.54/13.94  tff(f_143, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 22.54/13.94  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 22.54/13.94  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 22.54/13.94  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 22.54/13.94  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 22.54/13.94  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 22.54/13.94  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 22.54/13.94  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 22.54/13.94  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 22.54/13.94  tff(f_49, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 22.54/13.94  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 22.54/13.94  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 22.54/13.94  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 22.54/13.94  tff(f_119, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 22.54/13.94  tff(c_62, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 22.54/13.94  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_168])).
% 22.54/13.94  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_168])).
% 22.54/13.94  tff(c_70, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 22.54/13.94  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 22.54/13.94  tff(c_427, plain, (![A_141, B_142, C_143]: (k2_relset_1(A_141, B_142, C_143)=k2_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 22.54/13.94  tff(c_444, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_427])).
% 22.54/13.94  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 22.54/13.94  tff(c_358, plain, (![A_136, B_137, C_138]: (k1_relset_1(A_136, B_137, C_138)=k1_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 22.54/13.94  tff(c_376, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_358])).
% 22.54/13.94  tff(c_60, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 22.54/13.94  tff(c_381, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_60])).
% 22.54/13.94  tff(c_450, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_444, c_381])).
% 22.54/13.94  tff(c_74, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 22.54/13.94  tff(c_66, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_168])).
% 22.54/13.94  tff(c_1189, plain, (![E_216, C_217, D_221, B_220, F_218, A_219]: (k1_funct_1(k8_funct_2(B_220, C_217, A_219, D_221, E_216), F_218)=k1_funct_1(E_216, k1_funct_1(D_221, F_218)) | k1_xboole_0=B_220 | ~r1_tarski(k2_relset_1(B_220, C_217, D_221), k1_relset_1(C_217, A_219, E_216)) | ~m1_subset_1(F_218, B_220) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(C_217, A_219))) | ~v1_funct_1(E_216) | ~m1_subset_1(D_221, k1_zfmisc_1(k2_zfmisc_1(B_220, C_217))) | ~v1_funct_2(D_221, B_220, C_217) | ~v1_funct_1(D_221) | v1_xboole_0(C_217))), inference(cnfTransformation, [status(thm)], [f_143])).
% 22.54/13.94  tff(c_1201, plain, (![B_220, D_221, F_218]: (k1_funct_1(k8_funct_2(B_220, '#skF_5', '#skF_3', D_221, '#skF_7'), F_218)=k1_funct_1('#skF_7', k1_funct_1(D_221, F_218)) | k1_xboole_0=B_220 | ~r1_tarski(k2_relset_1(B_220, '#skF_5', D_221), k1_relat_1('#skF_7')) | ~m1_subset_1(F_218, B_220) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_221, k1_zfmisc_1(k2_zfmisc_1(B_220, '#skF_5'))) | ~v1_funct_2(D_221, B_220, '#skF_5') | ~v1_funct_1(D_221) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_376, c_1189])).
% 22.54/13.94  tff(c_1218, plain, (![B_220, D_221, F_218]: (k1_funct_1(k8_funct_2(B_220, '#skF_5', '#skF_3', D_221, '#skF_7'), F_218)=k1_funct_1('#skF_7', k1_funct_1(D_221, F_218)) | k1_xboole_0=B_220 | ~r1_tarski(k2_relset_1(B_220, '#skF_5', D_221), k1_relat_1('#skF_7')) | ~m1_subset_1(F_218, B_220) | ~m1_subset_1(D_221, k1_zfmisc_1(k2_zfmisc_1(B_220, '#skF_5'))) | ~v1_funct_2(D_221, B_220, '#skF_5') | ~v1_funct_1(D_221) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1201])).
% 22.54/13.94  tff(c_1471, plain, (![B_244, D_245, F_246]: (k1_funct_1(k8_funct_2(B_244, '#skF_5', '#skF_3', D_245, '#skF_7'), F_246)=k1_funct_1('#skF_7', k1_funct_1(D_245, F_246)) | k1_xboole_0=B_244 | ~r1_tarski(k2_relset_1(B_244, '#skF_5', D_245), k1_relat_1('#skF_7')) | ~m1_subset_1(F_246, B_244) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(B_244, '#skF_5'))) | ~v1_funct_2(D_245, B_244, '#skF_5') | ~v1_funct_1(D_245))), inference(negUnitSimplification, [status(thm)], [c_74, c_1218])).
% 22.54/13.94  tff(c_1479, plain, (![F_246]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_246)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_246)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_246, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_1471])).
% 22.54/13.94  tff(c_1487, plain, (![F_246]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_246)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_246)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_246, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_450, c_1479])).
% 22.54/13.94  tff(c_1488, plain, (![F_246]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_246)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_246)) | ~m1_subset_1(F_246, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_1487])).
% 22.54/13.94  tff(c_290, plain, (![B_126, A_127]: (m1_subset_1(k1_tarski(B_126), k1_zfmisc_1(A_127)) | k1_xboole_0=A_127 | ~m1_subset_1(B_126, A_127))), inference(cnfTransformation, [status(thm)], [f_56])).
% 22.54/13.94  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 22.54/13.94  tff(c_495, plain, (![B_146, A_147]: (r1_tarski(k1_tarski(B_146), A_147) | k1_xboole_0=A_147 | ~m1_subset_1(B_146, A_147))), inference(resolution, [status(thm)], [c_290, c_22])).
% 22.54/13.94  tff(c_12, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | ~r1_tarski(k1_tarski(A_10), B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.54/13.94  tff(c_516, plain, (![B_146, A_147]: (r2_hidden(B_146, A_147) | k1_xboole_0=A_147 | ~m1_subset_1(B_146, A_147))), inference(resolution, [status(thm)], [c_495, c_12])).
% 22.54/13.94  tff(c_145, plain, (![C_95, A_96, B_97]: (v1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 22.54/13.94  tff(c_158, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_145])).
% 22.54/13.94  tff(c_445, plain, (k2_relset_1('#skF_5', '#skF_3', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_427])).
% 22.54/13.94  tff(c_544, plain, (![A_150, B_151, C_152]: (m1_subset_1(k2_relset_1(A_150, B_151, C_152), k1_zfmisc_1(B_151)) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.54/13.94  tff(c_565, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_445, c_544])).
% 22.54/13.94  tff(c_575, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_565])).
% 22.54/13.94  tff(c_585, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_3')), inference(resolution, [status(thm)], [c_575, c_22])).
% 22.54/13.94  tff(c_26, plain, (![B_21, A_20]: (v5_relat_1(B_21, A_20) | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.54/13.94  tff(c_594, plain, (v5_relat_1('#skF_7', '#skF_3') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_585, c_26])).
% 22.54/13.94  tff(c_599, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_594])).
% 22.54/13.94  tff(c_157, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_145])).
% 22.54/13.94  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.54/13.94  tff(c_114, plain, (![A_90, B_91]: (k2_xboole_0(k1_tarski(A_90), B_91)=B_91 | ~r2_hidden(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_46])).
% 22.54/13.94  tff(c_18, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.54/13.94  tff(c_126, plain, (![B_92, A_93]: (k1_xboole_0!=B_92 | ~r2_hidden(A_93, B_92))), inference(superposition, [status(thm), theory('equality')], [c_114, c_18])).
% 22.54/13.94  tff(c_136, plain, (![A_94]: (k1_xboole_0!=A_94 | v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_4, c_126])).
% 22.54/13.94  tff(c_144, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_136, c_74])).
% 22.54/13.94  tff(c_375, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_358])).
% 22.54/13.94  tff(c_960, plain, (![B_194, A_195, C_196]: (k1_xboole_0=B_194 | k1_relset_1(A_195, B_194, C_196)=A_195 | ~v1_funct_2(C_196, A_195, B_194) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 22.54/13.94  tff(c_975, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_960])).
% 22.54/13.94  tff(c_984, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_375, c_975])).
% 22.54/13.94  tff(c_985, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_144, c_984])).
% 22.54/13.94  tff(c_624, plain, (![B_153, A_154]: (r2_hidden(k1_funct_1(B_153, A_154), k2_relat_1(B_153)) | ~r2_hidden(A_154, k1_relat_1(B_153)) | ~v1_funct_1(B_153) | ~v1_relat_1(B_153))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.54/13.94  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.54/13.94  tff(c_9926, plain, (![B_953, A_954, B_955]: (r2_hidden(k1_funct_1(B_953, A_954), B_955) | ~r1_tarski(k2_relat_1(B_953), B_955) | ~r2_hidden(A_954, k1_relat_1(B_953)) | ~v1_funct_1(B_953) | ~v1_relat_1(B_953))), inference(resolution, [status(thm)], [c_624, c_6])).
% 22.54/13.94  tff(c_52, plain, (![A_39, B_40, C_42]: (k7_partfun1(A_39, B_40, C_42)=k1_funct_1(B_40, C_42) | ~r2_hidden(C_42, k1_relat_1(B_40)) | ~v1_funct_1(B_40) | ~v5_relat_1(B_40, A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_119])).
% 22.54/13.94  tff(c_27005, plain, (![A_1755, B_1756, B_1757, A_1758]: (k7_partfun1(A_1755, B_1756, k1_funct_1(B_1757, A_1758))=k1_funct_1(B_1756, k1_funct_1(B_1757, A_1758)) | ~v1_funct_1(B_1756) | ~v5_relat_1(B_1756, A_1755) | ~v1_relat_1(B_1756) | ~r1_tarski(k2_relat_1(B_1757), k1_relat_1(B_1756)) | ~r2_hidden(A_1758, k1_relat_1(B_1757)) | ~v1_funct_1(B_1757) | ~v1_relat_1(B_1757))), inference(resolution, [status(thm)], [c_9926, c_52])).
% 22.54/13.94  tff(c_27028, plain, (![A_1755, A_1758]: (k7_partfun1(A_1755, '#skF_7', k1_funct_1('#skF_6', A_1758))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_1758)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_1755) | ~v1_relat_1('#skF_7') | ~r2_hidden(A_1758, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_450, c_27005])).
% 22.54/13.94  tff(c_48231, plain, (![A_2405, A_2406]: (k7_partfun1(A_2405, '#skF_7', k1_funct_1('#skF_6', A_2406))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_2406)) | ~v5_relat_1('#skF_7', A_2405) | ~r2_hidden(A_2406, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_72, c_985, c_158, c_66, c_27028])).
% 22.54/13.94  tff(c_56, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_168])).
% 22.54/13.94  tff(c_48237, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48231, c_56])).
% 22.54/13.94  tff(c_48243, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_48237])).
% 22.54/13.94  tff(c_48387, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_48243])).
% 22.54/13.94  tff(c_48390, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_516, c_48387])).
% 22.54/13.94  tff(c_48393, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_48390])).
% 22.54/13.94  tff(c_48395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_48393])).
% 22.54/13.94  tff(c_48396, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_48243])).
% 22.54/13.94  tff(c_52303, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1488, c_48396])).
% 22.54/13.94  tff(c_52310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_52303])).
% 22.54/13.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.54/13.94  
% 22.54/13.94  Inference rules
% 22.54/13.94  ----------------------
% 22.54/13.94  #Ref     : 9
% 22.54/13.94  #Sup     : 11654
% 22.54/13.94  #Fact    : 0
% 22.54/13.94  #Define  : 0
% 22.54/13.94  #Split   : 100
% 22.54/13.94  #Chain   : 0
% 22.54/13.94  #Close   : 0
% 22.54/13.94  
% 22.54/13.94  Ordering : KBO
% 22.54/13.94  
% 22.54/13.94  Simplification rules
% 22.54/13.94  ----------------------
% 22.54/13.94  #Subsume      : 6411
% 22.54/13.94  #Demod        : 2492
% 22.54/13.94  #Tautology    : 1023
% 22.54/13.94  #SimpNegUnit  : 1480
% 22.54/13.94  #BackRed      : 784
% 22.54/13.94  
% 22.54/13.94  #Partial instantiations: 0
% 22.54/13.94  #Strategies tried      : 1
% 22.54/13.94  
% 22.54/13.94  Timing (in seconds)
% 22.54/13.94  ----------------------
% 22.54/13.94  Preprocessing        : 0.36
% 22.54/13.94  Parsing              : 0.18
% 22.54/13.94  CNF conversion       : 0.03
% 22.54/13.94  Main loop            : 12.82
% 22.54/13.94  Inferencing          : 2.75
% 22.54/13.94  Reduction            : 4.73
% 22.54/13.94  Demodulation         : 3.29
% 22.54/13.94  BG Simplification    : 0.21
% 22.54/13.94  Subsumption          : 4.20
% 22.54/13.94  Abstraction          : 0.35
% 22.54/13.94  MUC search           : 0.00
% 22.54/13.94  Cooper               : 0.00
% 22.54/13.94  Total                : 13.21
% 22.54/13.94  Index Insertion      : 0.00
% 22.54/13.94  Index Deletion       : 0.00
% 22.54/13.94  Index Matching       : 0.00
% 22.54/13.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
