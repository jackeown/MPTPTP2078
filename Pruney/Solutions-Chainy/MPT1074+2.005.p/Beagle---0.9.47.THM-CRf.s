%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:06 EST 2020

% Result     : Theorem 10.38s
% Output     : CNFRefutation 10.38s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 508 expanded)
%              Number of leaves         :   34 ( 190 expanded)
%              Depth                    :   23
%              Number of atoms          :  215 (1983 expanded)
%              Number of equality atoms :   20 ( 102 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(f_111,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_89,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_142,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_151,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_142])).

tff(c_36,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_152,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_36])).

tff(c_60,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_93,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_240,plain,(
    ! [C_94,B_95] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_94),B_95,C_94),k1_relat_1(C_94))
      | v1_funct_2(C_94,k1_relat_1(C_94),B_95)
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    ! [A_67,B_2,A_1] :
      ( m1_subset_1(A_67,B_2)
      | ~ r2_hidden(A_67,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_243,plain,(
    ! [C_94,B_95,B_2] :
      ( m1_subset_1('#skF_1'(k1_relat_1(C_94),B_95,C_94),B_2)
      | ~ r1_tarski(k1_relat_1(C_94),B_2)
      | v1_funct_2(C_94,k1_relat_1(C_94),B_95)
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_240,c_134])).

tff(c_588,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( k3_funct_2(A_164,B_165,C_166,D_167) = k1_funct_1(C_166,D_167)
      | ~ m1_subset_1(D_167,A_164)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_2(C_166,A_164,B_165)
      | ~ v1_funct_1(C_166)
      | v1_xboole_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7645,plain,(
    ! [B_1148,B_1150,B_1151,C_1149,C_1152] :
      ( k3_funct_2(B_1151,B_1148,C_1152,'#skF_1'(k1_relat_1(C_1149),B_1150,C_1149)) = k1_funct_1(C_1152,'#skF_1'(k1_relat_1(C_1149),B_1150,C_1149))
      | ~ m1_subset_1(C_1152,k1_zfmisc_1(k2_zfmisc_1(B_1151,B_1148)))
      | ~ v1_funct_2(C_1152,B_1151,B_1148)
      | ~ v1_funct_1(C_1152)
      | v1_xboole_0(B_1151)
      | ~ r1_tarski(k1_relat_1(C_1149),B_1151)
      | v1_funct_2(C_1149,k1_relat_1(C_1149),B_1150)
      | ~ v1_funct_1(C_1149)
      | ~ v1_relat_1(C_1149) ) ),
    inference(resolution,[status(thm)],[c_243,c_588])).

tff(c_7708,plain,(
    ! [C_1149,B_1150] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_1149),B_1150,C_1149)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_1149),B_1150,C_1149))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski(k1_relat_1(C_1149),'#skF_3')
      | v1_funct_2(C_1149,k1_relat_1(C_1149),B_1150)
      | ~ v1_funct_1(C_1149)
      | ~ v1_relat_1(C_1149) ) ),
    inference(resolution,[status(thm)],[c_40,c_7645])).

tff(c_7732,plain,(
    ! [C_1149,B_1150] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_1149),B_1150,C_1149)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_1149),B_1150,C_1149))
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski(k1_relat_1(C_1149),'#skF_3')
      | v1_funct_2(C_1149,k1_relat_1(C_1149),B_1150)
      | ~ v1_funct_1(C_1149)
      | ~ v1_relat_1(C_1149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_7708])).

tff(c_7734,plain,(
    ! [C_1153,B_1154] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_1153),B_1154,C_1153)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_1153),B_1154,C_1153))
      | ~ r1_tarski(k1_relat_1(C_1153),'#skF_3')
      | v1_funct_2(C_1153,k1_relat_1(C_1153),B_1154)
      | ~ v1_funct_1(C_1153)
      | ~ v1_relat_1(C_1153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_7732])).

tff(c_38,plain,(
    ! [E_39] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_39),'#skF_2')
      | ~ m1_subset_1(E_39,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7784,plain,(
    ! [C_1155,B_1156] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_1155),B_1156,C_1155)),'#skF_2')
      | ~ m1_subset_1('#skF_1'(k1_relat_1(C_1155),B_1156,C_1155),'#skF_3')
      | ~ r1_tarski(k1_relat_1(C_1155),'#skF_3')
      | v1_funct_2(C_1155,k1_relat_1(C_1155),B_1156)
      | ~ v1_funct_1(C_1155)
      | ~ v1_relat_1(C_1155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7734,c_38])).

tff(c_28,plain,(
    ! [C_26,B_25] :
      ( ~ r2_hidden(k1_funct_1(C_26,'#skF_1'(k1_relat_1(C_26),B_25,C_26)),B_25)
      | v1_funct_2(C_26,k1_relat_1(C_26),B_25)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7792,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_7784,c_28])).

tff(c_7800,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_44,c_7792])).

tff(c_7802,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7800])).

tff(c_7883,plain,
    ( ~ v4_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_7802])).

tff(c_7887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_102,c_7883])).

tff(c_7889,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_7800])).

tff(c_396,plain,(
    ! [C_140,B_141] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_140),B_141,C_140),k1_relat_1(C_140))
      | m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_140),B_141)))
      | ~ v1_funct_1(C_140)
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_502,plain,(
    ! [C_161,B_162,B_163] :
      ( m1_subset_1('#skF_1'(k1_relat_1(C_161),B_162,C_161),B_163)
      | ~ r1_tarski(k1_relat_1(C_161),B_163)
      | m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_161),B_162)))
      | ~ v1_funct_1(C_161)
      | ~ v1_relat_1(C_161) ) ),
    inference(resolution,[status(thm)],[c_396,c_134])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_582,plain,(
    ! [C_161,B_162,B_163] :
      ( k2_relset_1(k1_relat_1(C_161),B_162,C_161) = k2_relat_1(C_161)
      | m1_subset_1('#skF_1'(k1_relat_1(C_161),B_162,C_161),B_163)
      | ~ r1_tarski(k1_relat_1(C_161),B_163)
      | ~ v1_funct_1(C_161)
      | ~ v1_relat_1(C_161) ) ),
    inference(resolution,[status(thm)],[c_502,c_20])).

tff(c_7888,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_7800])).

tff(c_7896,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7888])).

tff(c_7906,plain,
    ( k2_relset_1(k1_relat_1('#skF_5'),'#skF_2','#skF_5') = k2_relat_1('#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_582,c_7896])).

tff(c_7926,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_44,c_7889,c_7906])).

tff(c_200,plain,(
    ! [A_91,B_92,C_93] :
      ( m1_subset_1(k2_relset_1(A_91,B_92,C_93),k1_zfmisc_1(B_92))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_230,plain,(
    ! [A_91,B_92,C_93] :
      ( r1_tarski(k2_relset_1(A_91,B_92,C_93),B_92)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(resolution,[status(thm)],[c_200,c_2])).

tff(c_581,plain,(
    ! [C_161,B_162,B_163] :
      ( r1_tarski(k2_relset_1(k1_relat_1(C_161),B_162,C_161),B_162)
      | m1_subset_1('#skF_1'(k1_relat_1(C_161),B_162,C_161),B_163)
      | ~ r1_tarski(k1_relat_1(C_161),B_163)
      | ~ v1_funct_1(C_161)
      | ~ v1_relat_1(C_161) ) ),
    inference(resolution,[status(thm)],[c_502,c_230])).

tff(c_7954,plain,(
    ! [B_163] :
      ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
      | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),B_163)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_163)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7926,c_581])).

tff(c_7970,plain,(
    ! [B_163] :
      ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
      | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),B_163)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_44,c_7954])).

tff(c_7984,plain,(
    ! [B_1166] :
      ( m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),B_1166)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_1166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_7970])).

tff(c_7987,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_7984,c_7896])).

tff(c_8050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7889,c_7987])).

tff(c_8052,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_7888])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( k3_funct_2(A_20,B_21,C_22,D_23) = k1_funct_1(C_22,D_23)
      | ~ m1_subset_1(D_23,A_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8054,plain,(
    ! [B_21,C_22] :
      ( k3_funct_2('#skF_3',B_21,C_22,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1(C_22,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_21)))
      | ~ v1_funct_2(C_22,'#skF_3',B_21)
      | ~ v1_funct_1(C_22)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8052,c_22])).

tff(c_8065,plain,(
    ! [B_1172,C_1173] :
      ( k3_funct_2('#skF_3',B_1172,C_1173,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1(C_1173,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
      | ~ m1_subset_1(C_1173,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1172)))
      | ~ v1_funct_2(C_1173,'#skF_3',B_1172)
      | ~ v1_funct_1(C_1173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_8054])).

tff(c_8144,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_8065])).

tff(c_8166,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_8144])).

tff(c_8211,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8166,c_38])).

tff(c_8247,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8052,c_8211])).

tff(c_24,plain,(
    ! [C_26,B_25] :
      ( ~ r2_hidden(k1_funct_1(C_26,'#skF_1'(k1_relat_1(C_26),B_25,C_26)),B_25)
      | m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_26),B_25)))
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8254,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8247,c_24])).

tff(c_8262,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_44,c_8254])).

tff(c_8421,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8262,c_20])).

tff(c_8420,plain,(
    r1_tarski(k2_relset_1(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8262,c_230])).

tff(c_8491,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8421,c_8420])).

tff(c_8493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_8491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:21:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.38/4.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/4.15  
% 10.38/4.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/4.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 10.38/4.15  
% 10.38/4.15  %Foreground sorts:
% 10.38/4.15  
% 10.38/4.15  
% 10.38/4.15  %Background operators:
% 10.38/4.15  
% 10.38/4.15  
% 10.38/4.15  %Foreground operators:
% 10.38/4.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.38/4.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.38/4.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.38/4.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.38/4.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.38/4.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.38/4.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.38/4.15  tff('#skF_5', type, '#skF_5': $i).
% 10.38/4.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.38/4.15  tff('#skF_2', type, '#skF_2': $i).
% 10.38/4.15  tff('#skF_3', type, '#skF_3': $i).
% 10.38/4.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.38/4.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.38/4.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.38/4.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.38/4.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.38/4.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.38/4.15  tff('#skF_4', type, '#skF_4': $i).
% 10.38/4.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.38/4.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.38/4.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.38/4.15  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 10.38/4.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.38/4.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.38/4.15  
% 10.38/4.17  tff(f_111, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 10.38/4.17  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.38/4.17  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.38/4.17  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.38/4.17  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.38/4.17  tff(f_89, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 10.38/4.17  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.38/4.17  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 10.38/4.17  tff(f_72, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 10.38/4.17  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 10.38/4.17  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.38/4.17  tff(c_142, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.38/4.17  tff(c_151, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_142])).
% 10.38/4.17  tff(c_36, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.38/4.17  tff(c_152, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_36])).
% 10.38/4.17  tff(c_60, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.38/4.17  tff(c_69, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_60])).
% 10.38/4.17  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.38/4.17  tff(c_93, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.38/4.17  tff(c_102, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_93])).
% 10.38/4.17  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.38/4.17  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.38/4.17  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.38/4.17  tff(c_240, plain, (![C_94, B_95]: (r2_hidden('#skF_1'(k1_relat_1(C_94), B_95, C_94), k1_relat_1(C_94)) | v1_funct_2(C_94, k1_relat_1(C_94), B_95) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.38/4.17  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.38/4.17  tff(c_129, plain, (![A_67, C_68, B_69]: (m1_subset_1(A_67, C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.38/4.17  tff(c_134, plain, (![A_67, B_2, A_1]: (m1_subset_1(A_67, B_2) | ~r2_hidden(A_67, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_129])).
% 10.38/4.17  tff(c_243, plain, (![C_94, B_95, B_2]: (m1_subset_1('#skF_1'(k1_relat_1(C_94), B_95, C_94), B_2) | ~r1_tarski(k1_relat_1(C_94), B_2) | v1_funct_2(C_94, k1_relat_1(C_94), B_95) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_240, c_134])).
% 10.38/4.17  tff(c_588, plain, (![A_164, B_165, C_166, D_167]: (k3_funct_2(A_164, B_165, C_166, D_167)=k1_funct_1(C_166, D_167) | ~m1_subset_1(D_167, A_164) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~v1_funct_2(C_166, A_164, B_165) | ~v1_funct_1(C_166) | v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.38/4.17  tff(c_7645, plain, (![B_1148, B_1150, B_1151, C_1149, C_1152]: (k3_funct_2(B_1151, B_1148, C_1152, '#skF_1'(k1_relat_1(C_1149), B_1150, C_1149))=k1_funct_1(C_1152, '#skF_1'(k1_relat_1(C_1149), B_1150, C_1149)) | ~m1_subset_1(C_1152, k1_zfmisc_1(k2_zfmisc_1(B_1151, B_1148))) | ~v1_funct_2(C_1152, B_1151, B_1148) | ~v1_funct_1(C_1152) | v1_xboole_0(B_1151) | ~r1_tarski(k1_relat_1(C_1149), B_1151) | v1_funct_2(C_1149, k1_relat_1(C_1149), B_1150) | ~v1_funct_1(C_1149) | ~v1_relat_1(C_1149))), inference(resolution, [status(thm)], [c_243, c_588])).
% 10.38/4.17  tff(c_7708, plain, (![C_1149, B_1150]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_1149), B_1150, C_1149))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_1149), B_1150, C_1149)) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~r1_tarski(k1_relat_1(C_1149), '#skF_3') | v1_funct_2(C_1149, k1_relat_1(C_1149), B_1150) | ~v1_funct_1(C_1149) | ~v1_relat_1(C_1149))), inference(resolution, [status(thm)], [c_40, c_7645])).
% 10.38/4.17  tff(c_7732, plain, (![C_1149, B_1150]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_1149), B_1150, C_1149))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_1149), B_1150, C_1149)) | v1_xboole_0('#skF_3') | ~r1_tarski(k1_relat_1(C_1149), '#skF_3') | v1_funct_2(C_1149, k1_relat_1(C_1149), B_1150) | ~v1_funct_1(C_1149) | ~v1_relat_1(C_1149))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_7708])).
% 10.38/4.17  tff(c_7734, plain, (![C_1153, B_1154]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_1153), B_1154, C_1153))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_1153), B_1154, C_1153)) | ~r1_tarski(k1_relat_1(C_1153), '#skF_3') | v1_funct_2(C_1153, k1_relat_1(C_1153), B_1154) | ~v1_funct_1(C_1153) | ~v1_relat_1(C_1153))), inference(negUnitSimplification, [status(thm)], [c_48, c_7732])).
% 10.38/4.17  tff(c_38, plain, (![E_39]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_39), '#skF_2') | ~m1_subset_1(E_39, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.38/4.17  tff(c_7784, plain, (![C_1155, B_1156]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_1155), B_1156, C_1155)), '#skF_2') | ~m1_subset_1('#skF_1'(k1_relat_1(C_1155), B_1156, C_1155), '#skF_3') | ~r1_tarski(k1_relat_1(C_1155), '#skF_3') | v1_funct_2(C_1155, k1_relat_1(C_1155), B_1156) | ~v1_funct_1(C_1155) | ~v1_relat_1(C_1155))), inference(superposition, [status(thm), theory('equality')], [c_7734, c_38])).
% 10.38/4.17  tff(c_28, plain, (![C_26, B_25]: (~r2_hidden(k1_funct_1(C_26, '#skF_1'(k1_relat_1(C_26), B_25, C_26)), B_25) | v1_funct_2(C_26, k1_relat_1(C_26), B_25) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.38/4.17  tff(c_7792, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_7784, c_28])).
% 10.38/4.17  tff(c_7800, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_44, c_7792])).
% 10.38/4.17  tff(c_7802, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_7800])).
% 10.38/4.17  tff(c_7883, plain, (~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_7802])).
% 10.38/4.17  tff(c_7887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_102, c_7883])).
% 10.38/4.17  tff(c_7889, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_7800])).
% 10.38/4.17  tff(c_396, plain, (![C_140, B_141]: (r2_hidden('#skF_1'(k1_relat_1(C_140), B_141, C_140), k1_relat_1(C_140)) | m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_140), B_141))) | ~v1_funct_1(C_140) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.38/4.17  tff(c_502, plain, (![C_161, B_162, B_163]: (m1_subset_1('#skF_1'(k1_relat_1(C_161), B_162, C_161), B_163) | ~r1_tarski(k1_relat_1(C_161), B_163) | m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_161), B_162))) | ~v1_funct_1(C_161) | ~v1_relat_1(C_161))), inference(resolution, [status(thm)], [c_396, c_134])).
% 10.38/4.17  tff(c_20, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.38/4.17  tff(c_582, plain, (![C_161, B_162, B_163]: (k2_relset_1(k1_relat_1(C_161), B_162, C_161)=k2_relat_1(C_161) | m1_subset_1('#skF_1'(k1_relat_1(C_161), B_162, C_161), B_163) | ~r1_tarski(k1_relat_1(C_161), B_163) | ~v1_funct_1(C_161) | ~v1_relat_1(C_161))), inference(resolution, [status(thm)], [c_502, c_20])).
% 10.38/4.17  tff(c_7888, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_7800])).
% 10.38/4.17  tff(c_7896, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_7888])).
% 10.38/4.17  tff(c_7906, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')=k2_relat_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_582, c_7896])).
% 10.38/4.17  tff(c_7926, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_44, c_7889, c_7906])).
% 10.38/4.17  tff(c_200, plain, (![A_91, B_92, C_93]: (m1_subset_1(k2_relset_1(A_91, B_92, C_93), k1_zfmisc_1(B_92)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.38/4.17  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.38/4.17  tff(c_230, plain, (![A_91, B_92, C_93]: (r1_tarski(k2_relset_1(A_91, B_92, C_93), B_92) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(resolution, [status(thm)], [c_200, c_2])).
% 10.38/4.17  tff(c_581, plain, (![C_161, B_162, B_163]: (r1_tarski(k2_relset_1(k1_relat_1(C_161), B_162, C_161), B_162) | m1_subset_1('#skF_1'(k1_relat_1(C_161), B_162, C_161), B_163) | ~r1_tarski(k1_relat_1(C_161), B_163) | ~v1_funct_1(C_161) | ~v1_relat_1(C_161))), inference(resolution, [status(thm)], [c_502, c_230])).
% 10.38/4.17  tff(c_7954, plain, (![B_163]: (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), B_163) | ~r1_tarski(k1_relat_1('#skF_5'), B_163) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7926, c_581])).
% 10.38/4.17  tff(c_7970, plain, (![B_163]: (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), B_163) | ~r1_tarski(k1_relat_1('#skF_5'), B_163))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_44, c_7954])).
% 10.38/4.17  tff(c_7984, plain, (![B_1166]: (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), B_1166) | ~r1_tarski(k1_relat_1('#skF_5'), B_1166))), inference(negUnitSimplification, [status(thm)], [c_152, c_7970])).
% 10.38/4.17  tff(c_7987, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_7984, c_7896])).
% 10.38/4.17  tff(c_8050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7889, c_7987])).
% 10.38/4.17  tff(c_8052, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_7888])).
% 10.38/4.17  tff(c_22, plain, (![A_20, B_21, C_22, D_23]: (k3_funct_2(A_20, B_21, C_22, D_23)=k1_funct_1(C_22, D_23) | ~m1_subset_1(D_23, A_20) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.38/4.17  tff(c_8054, plain, (![B_21, C_22]: (k3_funct_2('#skF_3', B_21, C_22, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1(C_22, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_21))) | ~v1_funct_2(C_22, '#skF_3', B_21) | ~v1_funct_1(C_22) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_8052, c_22])).
% 10.38/4.17  tff(c_8065, plain, (![B_1172, C_1173]: (k3_funct_2('#skF_3', B_1172, C_1173, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1(C_1173, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~m1_subset_1(C_1173, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1172))) | ~v1_funct_2(C_1173, '#skF_3', B_1172) | ~v1_funct_1(C_1173))), inference(negUnitSimplification, [status(thm)], [c_48, c_8054])).
% 10.38/4.17  tff(c_8144, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_8065])).
% 10.38/4.17  tff(c_8166, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_8144])).
% 10.38/4.17  tff(c_8211, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8166, c_38])).
% 10.38/4.17  tff(c_8247, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8052, c_8211])).
% 10.38/4.17  tff(c_24, plain, (![C_26, B_25]: (~r2_hidden(k1_funct_1(C_26, '#skF_1'(k1_relat_1(C_26), B_25, C_26)), B_25) | m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_26), B_25))) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.38/4.17  tff(c_8254, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8247, c_24])).
% 10.38/4.17  tff(c_8262, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_44, c_8254])).
% 10.38/4.17  tff(c_8421, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8262, c_20])).
% 10.38/4.17  tff(c_8420, plain, (r1_tarski(k2_relset_1(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_8262, c_230])).
% 10.38/4.17  tff(c_8491, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8421, c_8420])).
% 10.38/4.17  tff(c_8493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_8491])).
% 10.38/4.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/4.17  
% 10.38/4.17  Inference rules
% 10.38/4.17  ----------------------
% 10.38/4.17  #Ref     : 0
% 10.38/4.17  #Sup     : 1944
% 10.38/4.17  #Fact    : 2
% 10.38/4.17  #Define  : 0
% 10.38/4.17  #Split   : 7
% 10.38/4.17  #Chain   : 0
% 10.38/4.17  #Close   : 0
% 10.38/4.17  
% 10.38/4.17  Ordering : KBO
% 10.38/4.17  
% 10.38/4.17  Simplification rules
% 10.38/4.17  ----------------------
% 10.38/4.17  #Subsume      : 150
% 10.38/4.17  #Demod        : 197
% 10.38/4.17  #Tautology    : 127
% 10.38/4.17  #SimpNegUnit  : 8
% 10.38/4.17  #BackRed      : 2
% 10.38/4.17  
% 10.38/4.17  #Partial instantiations: 0
% 10.38/4.17  #Strategies tried      : 1
% 10.38/4.17  
% 10.38/4.17  Timing (in seconds)
% 10.38/4.17  ----------------------
% 10.38/4.17  Preprocessing        : 0.32
% 10.38/4.17  Parsing              : 0.16
% 10.38/4.17  CNF conversion       : 0.02
% 10.38/4.17  Main loop            : 3.05
% 10.38/4.17  Inferencing          : 0.93
% 10.38/4.17  Reduction            : 0.65
% 10.38/4.17  Demodulation         : 0.43
% 10.38/4.17  BG Simplification    : 0.14
% 10.38/4.17  Subsumption          : 1.08
% 10.38/4.17  Abstraction          : 0.23
% 10.38/4.17  MUC search           : 0.00
% 10.38/4.17  Cooper               : 0.00
% 10.38/4.17  Total                : 3.40
% 10.38/4.17  Index Insertion      : 0.00
% 10.38/4.17  Index Deletion       : 0.00
% 10.38/4.17  Index Matching       : 0.00
% 10.38/4.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
