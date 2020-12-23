%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:37 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 518 expanded)
%              Number of leaves         :   35 ( 187 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 (1510 expanded)
%              Number of equality atoms :   54 ( 251 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_197,plain,(
    ! [C_77,B_78,A_79] :
      ( v1_xboole_0(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(B_78,A_79)))
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_209,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_197])).

tff(c_211,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_264,plain,(
    ! [A_88,B_89,D_90] :
      ( r2_relset_1(A_88,B_89,D_90,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_274,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_264])).

tff(c_80,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_92,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_80])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_366,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_381,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_366])).

tff(c_565,plain,(
    ! [B_133,A_134,C_135] :
      ( k1_xboole_0 = B_133
      | k1_relset_1(A_134,B_133,C_135) = A_134
      | ~ v1_funct_2(C_135,A_134,B_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_578,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_565])).

tff(c_586,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_381,c_578])).

tff(c_636,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_586])).

tff(c_93,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_80])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_382,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_366])).

tff(c_581,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_565])).

tff(c_589,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_382,c_581])).

tff(c_637,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_813,plain,(
    ! [A_161,B_162] :
      ( r2_hidden('#skF_2'(A_161,B_162),k1_relat_1(A_161))
      | B_162 = A_161
      | k1_relat_1(B_162) != k1_relat_1(A_161)
      | ~ v1_funct_1(B_162)
      | ~ v1_relat_1(B_162)
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_820,plain,(
    ! [B_162] :
      ( r2_hidden('#skF_2'('#skF_6',B_162),'#skF_3')
      | B_162 = '#skF_6'
      | k1_relat_1(B_162) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_162)
      | ~ v1_relat_1(B_162)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_813])).

tff(c_1016,plain,(
    ! [B_197] :
      ( r2_hidden('#skF_2'('#skF_6',B_197),'#skF_3')
      | B_197 = '#skF_6'
      | k1_relat_1(B_197) != '#skF_3'
      | ~ v1_funct_1(B_197)
      | ~ v1_relat_1(B_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_56,c_637,c_820])).

tff(c_50,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_5',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ r2_hidden(E_40,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1118,plain,(
    ! [B_207] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_207)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_207))
      | B_207 = '#skF_6'
      | k1_relat_1(B_207) != '#skF_3'
      | ~ v1_funct_1(B_207)
      | ~ v1_relat_1(B_207) ) ),
    inference(resolution,[status(thm)],[c_1016,c_50])).

tff(c_22,plain,(
    ! [B_17,A_13] :
      ( k1_funct_1(B_17,'#skF_2'(A_13,B_17)) != k1_funct_1(A_13,'#skF_2'(A_13,B_17))
      | B_17 = A_13
      | k1_relat_1(B_17) != k1_relat_1(A_13)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1125,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_22])).

tff(c_1132,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_62,c_636,c_93,c_56,c_637,c_636,c_1125])).

tff(c_48,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1145,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_48])).

tff(c_1156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_1145])).

tff(c_1157,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1178,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_8])).

tff(c_1180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_1178])).

tff(c_1181,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_586])).

tff(c_1202,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_8])).

tff(c_1204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_1202])).

tff(c_1206,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_210,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_197])).

tff(c_1228,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_210])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_142,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_162,plain,(
    ! [B_68,A_69,A_70] :
      ( ~ v1_xboole_0(B_68)
      | ~ r2_hidden(A_69,A_70)
      | ~ r1_tarski(A_70,B_68) ) ),
    inference(resolution,[status(thm)],[c_18,c_142])).

tff(c_166,plain,(
    ! [B_71,A_72,B_73] :
      ( ~ v1_xboole_0(B_71)
      | ~ r1_tarski(A_72,B_71)
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_175,plain,(
    ! [B_7,B_73] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_73) ) ),
    inference(resolution,[status(thm)],[c_14,c_166])).

tff(c_176,plain,(
    ! [B_74,B_75] :
      ( ~ v1_xboole_0(B_74)
      | r1_tarski(B_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_14,c_166])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1234,plain,(
    ! [B_212,B_211] :
      ( B_212 = B_211
      | ~ r1_tarski(B_211,B_212)
      | ~ v1_xboole_0(B_212) ) ),
    inference(resolution,[status(thm)],[c_176,c_10])).

tff(c_1252,plain,(
    ! [B_214,B_213] :
      ( B_214 = B_213
      | ~ v1_xboole_0(B_213)
      | ~ v1_xboole_0(B_214) ) ),
    inference(resolution,[status(thm)],[c_175,c_1234])).

tff(c_1265,plain,(
    ! [B_215] :
      ( B_215 = '#skF_6'
      | ~ v1_xboole_0(B_215) ) ),
    inference(resolution,[status(thm)],[c_1228,c_1252])).

tff(c_1280,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1206,c_1265])).

tff(c_1205,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_1281,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1205,c_1265])).

tff(c_1301,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_1281])).

tff(c_1292,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_48])).

tff(c_1346,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1301,c_1292])).

tff(c_1216,plain,(
    ! [A_208,B_209,D_210] :
      ( r2_relset_1(A_208,B_209,D_210,D_210)
      | ~ m1_subset_1(D_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1225,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1216])).

tff(c_1302,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1301,c_1301,c_1225])).

tff(c_1347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1346,c_1302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:31:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.63  
% 3.42/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.63  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.42/1.63  
% 3.42/1.63  %Foreground sorts:
% 3.42/1.63  
% 3.42/1.63  
% 3.42/1.63  %Background operators:
% 3.42/1.63  
% 3.42/1.63  
% 3.42/1.63  %Foreground operators:
% 3.42/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.42/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.42/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.42/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.42/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.42/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.42/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.42/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.42/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.42/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.42/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.42/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.42/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.42/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.63  
% 3.42/1.65  tff(f_130, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 3.42/1.65  tff(f_79, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.42/1.65  tff(f_91, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.42/1.65  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.42/1.65  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.42/1.65  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.42/1.65  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 3.42/1.65  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.42/1.65  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.42/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.42/1.65  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.42/1.65  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.42/1.65  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.42/1.65  tff(c_197, plain, (![C_77, B_78, A_79]: (v1_xboole_0(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(B_78, A_79))) | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.42/1.65  tff(c_209, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_197])).
% 3.42/1.65  tff(c_211, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_209])).
% 3.42/1.65  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.42/1.65  tff(c_264, plain, (![A_88, B_89, D_90]: (r2_relset_1(A_88, B_89, D_90, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.42/1.65  tff(c_274, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_264])).
% 3.42/1.65  tff(c_80, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.42/1.65  tff(c_92, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_80])).
% 3.42/1.65  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.42/1.65  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.42/1.65  tff(c_366, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.42/1.65  tff(c_381, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_366])).
% 3.42/1.65  tff(c_565, plain, (![B_133, A_134, C_135]: (k1_xboole_0=B_133 | k1_relset_1(A_134, B_133, C_135)=A_134 | ~v1_funct_2(C_135, A_134, B_133) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.42/1.65  tff(c_578, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_565])).
% 3.42/1.65  tff(c_586, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_381, c_578])).
% 3.42/1.65  tff(c_636, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_586])).
% 3.42/1.65  tff(c_93, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_80])).
% 3.42/1.65  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.42/1.65  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.42/1.65  tff(c_382, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_366])).
% 3.42/1.65  tff(c_581, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_565])).
% 3.42/1.65  tff(c_589, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_382, c_581])).
% 3.42/1.65  tff(c_637, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_589])).
% 3.42/1.65  tff(c_813, plain, (![A_161, B_162]: (r2_hidden('#skF_2'(A_161, B_162), k1_relat_1(A_161)) | B_162=A_161 | k1_relat_1(B_162)!=k1_relat_1(A_161) | ~v1_funct_1(B_162) | ~v1_relat_1(B_162) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.65  tff(c_820, plain, (![B_162]: (r2_hidden('#skF_2'('#skF_6', B_162), '#skF_3') | B_162='#skF_6' | k1_relat_1(B_162)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_162) | ~v1_relat_1(B_162) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_637, c_813])).
% 3.42/1.65  tff(c_1016, plain, (![B_197]: (r2_hidden('#skF_2'('#skF_6', B_197), '#skF_3') | B_197='#skF_6' | k1_relat_1(B_197)!='#skF_3' | ~v1_funct_1(B_197) | ~v1_relat_1(B_197))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_56, c_637, c_820])).
% 3.42/1.65  tff(c_50, plain, (![E_40]: (k1_funct_1('#skF_5', E_40)=k1_funct_1('#skF_6', E_40) | ~r2_hidden(E_40, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.42/1.65  tff(c_1118, plain, (![B_207]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_207))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_207)) | B_207='#skF_6' | k1_relat_1(B_207)!='#skF_3' | ~v1_funct_1(B_207) | ~v1_relat_1(B_207))), inference(resolution, [status(thm)], [c_1016, c_50])).
% 3.42/1.65  tff(c_22, plain, (![B_17, A_13]: (k1_funct_1(B_17, '#skF_2'(A_13, B_17))!=k1_funct_1(A_13, '#skF_2'(A_13, B_17)) | B_17=A_13 | k1_relat_1(B_17)!=k1_relat_1(A_13) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.65  tff(c_1125, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1118, c_22])).
% 3.42/1.65  tff(c_1132, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_62, c_636, c_93, c_56, c_637, c_636, c_1125])).
% 3.42/1.65  tff(c_48, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.42/1.65  tff(c_1145, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_48])).
% 3.42/1.65  tff(c_1156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_1145])).
% 3.42/1.65  tff(c_1157, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_589])).
% 3.42/1.65  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.42/1.65  tff(c_1178, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1157, c_8])).
% 3.42/1.65  tff(c_1180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_1178])).
% 3.42/1.65  tff(c_1181, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_586])).
% 3.42/1.65  tff(c_1202, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1181, c_8])).
% 3.42/1.65  tff(c_1204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_1202])).
% 3.42/1.65  tff(c_1206, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_209])).
% 3.42/1.65  tff(c_210, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_197])).
% 3.42/1.65  tff(c_1228, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1206, c_210])).
% 3.42/1.65  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.42/1.65  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.42/1.65  tff(c_142, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.42/1.65  tff(c_162, plain, (![B_68, A_69, A_70]: (~v1_xboole_0(B_68) | ~r2_hidden(A_69, A_70) | ~r1_tarski(A_70, B_68))), inference(resolution, [status(thm)], [c_18, c_142])).
% 3.42/1.65  tff(c_166, plain, (![B_71, A_72, B_73]: (~v1_xboole_0(B_71) | ~r1_tarski(A_72, B_71) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_6, c_162])).
% 3.42/1.65  tff(c_175, plain, (![B_7, B_73]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_73))), inference(resolution, [status(thm)], [c_14, c_166])).
% 3.42/1.65  tff(c_176, plain, (![B_74, B_75]: (~v1_xboole_0(B_74) | r1_tarski(B_74, B_75))), inference(resolution, [status(thm)], [c_14, c_166])).
% 3.42/1.65  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.65  tff(c_1234, plain, (![B_212, B_211]: (B_212=B_211 | ~r1_tarski(B_211, B_212) | ~v1_xboole_0(B_212))), inference(resolution, [status(thm)], [c_176, c_10])).
% 3.42/1.65  tff(c_1252, plain, (![B_214, B_213]: (B_214=B_213 | ~v1_xboole_0(B_213) | ~v1_xboole_0(B_214))), inference(resolution, [status(thm)], [c_175, c_1234])).
% 3.42/1.65  tff(c_1265, plain, (![B_215]: (B_215='#skF_6' | ~v1_xboole_0(B_215))), inference(resolution, [status(thm)], [c_1228, c_1252])).
% 3.42/1.65  tff(c_1280, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_1206, c_1265])).
% 3.42/1.65  tff(c_1205, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_209])).
% 3.42/1.65  tff(c_1281, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1205, c_1265])).
% 3.42/1.65  tff(c_1301, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1280, c_1281])).
% 3.42/1.65  tff(c_1292, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1280, c_48])).
% 3.42/1.65  tff(c_1346, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1301, c_1292])).
% 3.42/1.65  tff(c_1216, plain, (![A_208, B_209, D_210]: (r2_relset_1(A_208, B_209, D_210, D_210) | ~m1_subset_1(D_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.42/1.65  tff(c_1225, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_1216])).
% 3.42/1.65  tff(c_1302, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1301, c_1301, c_1225])).
% 3.42/1.65  tff(c_1347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1346, c_1302])).
% 3.42/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.65  
% 3.42/1.65  Inference rules
% 3.42/1.65  ----------------------
% 3.42/1.65  #Ref     : 1
% 3.42/1.65  #Sup     : 264
% 3.42/1.65  #Fact    : 0
% 3.42/1.65  #Define  : 0
% 3.42/1.65  #Split   : 9
% 3.42/1.65  #Chain   : 0
% 3.42/1.65  #Close   : 0
% 3.42/1.65  
% 3.42/1.65  Ordering : KBO
% 3.42/1.65  
% 3.42/1.65  Simplification rules
% 3.42/1.65  ----------------------
% 3.42/1.65  #Subsume      : 51
% 3.42/1.65  #Demod        : 246
% 3.42/1.65  #Tautology    : 131
% 3.42/1.65  #SimpNegUnit  : 5
% 3.42/1.65  #BackRed      : 75
% 3.42/1.65  
% 3.42/1.65  #Partial instantiations: 0
% 3.42/1.65  #Strategies tried      : 1
% 3.42/1.65  
% 3.42/1.65  Timing (in seconds)
% 3.42/1.65  ----------------------
% 3.42/1.65  Preprocessing        : 0.32
% 3.42/1.65  Parsing              : 0.16
% 3.42/1.65  CNF conversion       : 0.02
% 3.42/1.65  Main loop            : 0.46
% 3.42/1.65  Inferencing          : 0.16
% 3.42/1.65  Reduction            : 0.15
% 3.42/1.65  Demodulation         : 0.11
% 3.42/1.65  BG Simplification    : 0.02
% 3.42/1.65  Subsumption          : 0.09
% 3.42/1.65  Abstraction          : 0.02
% 3.42/1.65  MUC search           : 0.00
% 3.42/1.65  Cooper               : 0.00
% 3.42/1.65  Total                : 0.82
% 3.42/1.65  Index Insertion      : 0.00
% 3.42/1.65  Index Deletion       : 0.00
% 3.42/1.65  Index Matching       : 0.00
% 3.42/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
