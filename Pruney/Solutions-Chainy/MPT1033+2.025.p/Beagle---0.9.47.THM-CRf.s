%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:53 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 942 expanded)
%              Number of leaves         :   30 ( 310 expanded)
%              Depth                    :   14
%              Number of atoms          :  258 (2595 expanded)
%              Number of equality atoms :   27 ( 461 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_211,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( r2_relset_1(A_72,B_73,C_74,C_74)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_235,plain,(
    ! [C_79] :
      ( r2_relset_1('#skF_3','#skF_4',C_79,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_211])).

tff(c_244,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_235])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( v1_xboole_0(k2_zfmisc_1(A_12,B_13))
      | ~ v1_xboole_0(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_2'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_46,B_47] :
      ( ~ v1_xboole_0(A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_59,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_73,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(B_40,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_73])).

tff(c_86,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_105,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_99,c_86])).

tff(c_110,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_105])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_178,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_partfun1(C_66,A_67)
      | ~ v1_funct_2(C_66,A_67,B_68)
      | ~ v1_funct_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | v1_xboole_0(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_188,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_178])).

tff(c_196,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_188])).

tff(c_197,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_196])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_185,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_178])).

tff(c_192,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_185])).

tff(c_193,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_192])).

tff(c_36,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_263,plain,(
    ! [D_81,C_82,A_83,B_84] :
      ( D_81 = C_82
      | ~ r1_partfun1(C_82,D_81)
      | ~ v1_partfun1(D_81,A_83)
      | ~ v1_partfun1(C_82,A_83)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_1(D_81)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_265,plain,(
    ! [A_83,B_84] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_83)
      | ~ v1_partfun1('#skF_5',A_83)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_263])).

tff(c_268,plain,(
    ! [A_83,B_84] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_83)
      | ~ v1_partfun1('#skF_5',A_83)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_265])).

tff(c_602,plain,(
    ! [A_131,B_132] :
      ( ~ v1_partfun1('#skF_6',A_131)
      | ~ v1_partfun1('#skF_5',A_131)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_608,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_44,c_602])).

tff(c_613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_197,c_193,c_608])).

tff(c_614,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_620,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_32])).

tff(c_630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_620])).

tff(c_631,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_636,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_44])).

tff(c_635,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_38])).

tff(c_641,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_18])).

tff(c_658,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_641])).

tff(c_761,plain,(
    ! [C_163,A_164,B_165] :
      ( v1_partfun1(C_163,A_164)
      | ~ v1_funct_2(C_163,A_164,B_165)
      | ~ v1_funct_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | v1_xboole_0(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_764,plain,(
    ! [C_163] :
      ( v1_partfun1(C_163,'#skF_3')
      | ~ v1_funct_2(C_163,'#skF_3','#skF_4')
      | ~ v1_funct_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1('#skF_6'))
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_761])).

tff(c_836,plain,(
    ! [C_184] :
      ( v1_partfun1(C_184,'#skF_3')
      | ~ v1_funct_2(C_184,'#skF_3','#skF_4')
      | ~ v1_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_764])).

tff(c_839,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_636,c_836])).

tff(c_849,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_839])).

tff(c_842,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_635,c_836])).

tff(c_852,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_842])).

tff(c_854,plain,(
    ! [D_185,C_186,A_187,B_188] :
      ( D_185 = C_186
      | ~ r1_partfun1(C_186,D_185)
      | ~ v1_partfun1(D_185,A_187)
      | ~ v1_partfun1(C_186,A_187)
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(D_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_856,plain,(
    ! [A_187,B_188] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_187)
      | ~ v1_partfun1('#skF_5',A_187)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_854])).

tff(c_859,plain,(
    ! [A_187,B_188] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_187)
      | ~ v1_partfun1('#skF_5',A_187)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_856])).

tff(c_1029,plain,(
    ! [A_214,B_215] :
      ( ~ v1_partfun1('#skF_6',A_214)
      | ~ v1_partfun1('#skF_5',A_214)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_214,B_215)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_1038,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_1029])).

tff(c_1044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_635,c_631,c_849,c_852,c_1038])).

tff(c_1045,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_67,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_633,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_67])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_647,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_633,c_12])).

tff(c_660,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_1050,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_660])).

tff(c_1061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1050])).

tff(c_1062,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_1066,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_32])).

tff(c_1210,plain,(
    ! [A_263,B_264,C_265,D_266] :
      ( r2_relset_1(A_263,B_264,C_265,C_265)
      | ~ m1_subset_1(D_266,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264)))
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1212,plain,(
    ! [C_265,D_266] :
      ( r2_relset_1('#skF_3','#skF_4',C_265,C_265)
      | ~ m1_subset_1(D_266,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_1210])).

tff(c_1216,plain,(
    ! [C_265,D_266] :
      ( r2_relset_1('#skF_3','#skF_4',C_265,C_265)
      | ~ m1_subset_1(D_266,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(C_265,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_1212])).

tff(c_1218,plain,(
    ! [D_266] : ~ m1_subset_1(D_266,k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1216])).

tff(c_1220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1218,c_635])).

tff(c_1222,plain,(
    ! [C_267] :
      ( r2_relset_1('#skF_3','#skF_4',C_267,C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1216])).

tff(c_1224,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_635,c_1222])).

tff(c_1231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1066,c_1224])).

tff(c_1232,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_1233,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_1272,plain,(
    ! [A_272,B_273] :
      ( r2_hidden('#skF_2'(A_272,B_273),A_272)
      | r1_tarski(A_272,B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1276,plain,(
    ! [A_272,B_273] :
      ( ~ v1_xboole_0(A_272)
      | r1_tarski(A_272,B_273) ) ),
    inference(resolution,[status(thm)],[c_1272,c_2])).

tff(c_1277,plain,(
    ! [A_274,B_275] :
      ( ~ v1_xboole_0(A_274)
      | r1_tarski(A_274,B_275) ) ),
    inference(resolution,[status(thm)],[c_1272,c_2])).

tff(c_1281,plain,(
    ! [B_276,A_277] :
      ( B_276 = A_277
      | ~ r1_tarski(B_276,A_277)
      | ~ v1_xboole_0(A_277) ) ),
    inference(resolution,[status(thm)],[c_1277,c_12])).

tff(c_1291,plain,(
    ! [B_278,A_279] :
      ( B_278 = A_279
      | ~ v1_xboole_0(B_278)
      | ~ v1_xboole_0(A_279) ) ),
    inference(resolution,[status(thm)],[c_1276,c_1281])).

tff(c_1301,plain,(
    ! [A_280] :
      ( A_280 = '#skF_4'
      | ~ v1_xboole_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_1233,c_1291])).

tff(c_1313,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1232,c_1301])).

tff(c_1319,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_1313,c_635])).

tff(c_1354,plain,(
    ! [A_283,B_284] :
      ( k2_zfmisc_1(A_283,B_284) = '#skF_4'
      | ~ v1_xboole_0(B_284) ) ),
    inference(resolution,[status(thm)],[c_18,c_1301])).

tff(c_1359,plain,(
    ! [A_283] : k2_zfmisc_1(A_283,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1233,c_1354])).

tff(c_1452,plain,(
    ! [A_306,B_307,C_308,D_309] :
      ( r2_relset_1(A_306,B_307,C_308,C_308)
      | ~ m1_subset_1(D_309,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307)))
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1456,plain,(
    ! [A_283,C_308,D_309] :
      ( r2_relset_1(A_283,'#skF_4',C_308,C_308)
      | ~ m1_subset_1(D_309,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_283,'#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1359,c_1452])).

tff(c_1460,plain,(
    ! [A_283,C_308,D_309] :
      ( r2_relset_1(A_283,'#skF_4',C_308,C_308)
      | ~ m1_subset_1(D_309,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_308,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_1456])).

tff(c_1497,plain,(
    ! [D_309] : ~ m1_subset_1(D_309,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1460])).

tff(c_1506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1497,c_1319])).

tff(c_1508,plain,(
    ! [A_328,C_329] :
      ( r2_relset_1(A_328,'#skF_4',C_329,C_329)
      | ~ m1_subset_1(C_329,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1460])).

tff(c_1514,plain,(
    ! [A_328] : r2_relset_1(A_328,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1319,c_1508])).

tff(c_1237,plain,(
    ! [A_268,B_269] :
      ( r2_hidden('#skF_2'(A_268,B_269),A_268)
      | r1_tarski(A_268,B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1242,plain,(
    ! [A_270,B_271] :
      ( ~ v1_xboole_0(A_270)
      | r1_tarski(A_270,B_271) ) ),
    inference(resolution,[status(thm)],[c_1237,c_2])).

tff(c_80,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_67,c_73])).

tff(c_1234,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_631,c_80])).

tff(c_1235,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1234])).

tff(c_1245,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1242,c_1235])).

tff(c_1251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1232,c_1245])).

tff(c_1252,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1234])).

tff(c_1256,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_32])).

tff(c_1315,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_1313,c_1256])).

tff(c_1518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1514,c_1315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.67  
% 3.57/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.67  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.57/1.67  
% 3.57/1.67  %Foreground sorts:
% 3.57/1.67  
% 3.57/1.67  
% 3.57/1.67  %Background operators:
% 3.57/1.67  
% 3.57/1.67  
% 3.57/1.67  %Foreground operators:
% 3.57/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.57/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.67  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.57/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.57/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.57/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.57/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.57/1.67  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.57/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.57/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.57/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.57/1.67  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.57/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.67  
% 3.57/1.69  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.57/1.69  tff(f_112, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 3.57/1.69  tff(f_58, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.57/1.69  tff(f_48, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.57/1.69  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.57/1.69  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.57/1.69  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.57/1.69  tff(f_72, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.57/1.69  tff(f_89, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 3.57/1.69  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.57/1.69  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.57/1.69  tff(c_211, plain, (![A_72, B_73, C_74, D_75]: (r2_relset_1(A_72, B_73, C_74, C_74) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.69  tff(c_235, plain, (![C_79]: (r2_relset_1('#skF_3', '#skF_4', C_79, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_38, c_211])).
% 3.57/1.69  tff(c_244, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_38, c_235])).
% 3.57/1.69  tff(c_18, plain, (![A_12, B_13]: (v1_xboole_0(k2_zfmisc_1(A_12, B_13)) | ~v1_xboole_0(B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.57/1.69  tff(c_88, plain, (![A_44, B_45]: (r2_hidden('#skF_2'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.57/1.69  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.69  tff(c_99, plain, (![A_46, B_47]: (~v1_xboole_0(A_46) | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_88, c_2])).
% 3.57/1.69  tff(c_59, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.57/1.69  tff(c_66, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_59])).
% 3.57/1.69  tff(c_73, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(B_40, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.57/1.69  tff(c_81, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_66, c_73])).
% 3.57/1.69  tff(c_86, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_81])).
% 3.57/1.69  tff(c_105, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_99, c_86])).
% 3.57/1.69  tff(c_110, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_18, c_105])).
% 3.57/1.69  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.57/1.69  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.57/1.69  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.57/1.69  tff(c_178, plain, (![C_66, A_67, B_68]: (v1_partfun1(C_66, A_67) | ~v1_funct_2(C_66, A_67, B_68) | ~v1_funct_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | v1_xboole_0(B_68))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.57/1.69  tff(c_188, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_178])).
% 3.57/1.69  tff(c_196, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_188])).
% 3.57/1.69  tff(c_197, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_110, c_196])).
% 3.57/1.69  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.57/1.69  tff(c_40, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.57/1.69  tff(c_185, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_178])).
% 3.57/1.69  tff(c_192, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_185])).
% 3.57/1.69  tff(c_193, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_110, c_192])).
% 3.57/1.69  tff(c_36, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.57/1.69  tff(c_263, plain, (![D_81, C_82, A_83, B_84]: (D_81=C_82 | ~r1_partfun1(C_82, D_81) | ~v1_partfun1(D_81, A_83) | ~v1_partfun1(C_82, A_83) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_1(D_81) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.57/1.69  tff(c_265, plain, (![A_83, B_84]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_83) | ~v1_partfun1('#skF_5', A_83) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_263])).
% 3.57/1.69  tff(c_268, plain, (![A_83, B_84]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_83) | ~v1_partfun1('#skF_5', A_83) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_265])).
% 3.57/1.69  tff(c_602, plain, (![A_131, B_132]: (~v1_partfun1('#skF_6', A_131) | ~v1_partfun1('#skF_5', A_131) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(splitLeft, [status(thm)], [c_268])).
% 3.57/1.69  tff(c_608, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_44, c_602])).
% 3.57/1.69  tff(c_613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_197, c_193, c_608])).
% 3.57/1.69  tff(c_614, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_268])).
% 3.57/1.69  tff(c_32, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.57/1.69  tff(c_620, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_614, c_32])).
% 3.57/1.69  tff(c_630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_244, c_620])).
% 3.57/1.69  tff(c_631, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_81])).
% 3.57/1.69  tff(c_636, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_631, c_44])).
% 3.57/1.69  tff(c_635, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_631, c_38])).
% 3.57/1.69  tff(c_641, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_631, c_18])).
% 3.57/1.69  tff(c_658, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_641])).
% 3.57/1.69  tff(c_761, plain, (![C_163, A_164, B_165]: (v1_partfun1(C_163, A_164) | ~v1_funct_2(C_163, A_164, B_165) | ~v1_funct_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | v1_xboole_0(B_165))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.57/1.69  tff(c_764, plain, (![C_163]: (v1_partfun1(C_163, '#skF_3') | ~v1_funct_2(C_163, '#skF_3', '#skF_4') | ~v1_funct_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1('#skF_6')) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_631, c_761])).
% 3.57/1.69  tff(c_836, plain, (![C_184]: (v1_partfun1(C_184, '#skF_3') | ~v1_funct_2(C_184, '#skF_3', '#skF_4') | ~v1_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_658, c_764])).
% 3.57/1.69  tff(c_839, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_636, c_836])).
% 3.57/1.69  tff(c_849, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_839])).
% 3.57/1.69  tff(c_842, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_635, c_836])).
% 3.57/1.69  tff(c_852, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_842])).
% 3.57/1.69  tff(c_854, plain, (![D_185, C_186, A_187, B_188]: (D_185=C_186 | ~r1_partfun1(C_186, D_185) | ~v1_partfun1(D_185, A_187) | ~v1_partfun1(C_186, A_187) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(D_185) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(C_186))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.57/1.69  tff(c_856, plain, (![A_187, B_188]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_187) | ~v1_partfun1('#skF_5', A_187) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_854])).
% 3.57/1.69  tff(c_859, plain, (![A_187, B_188]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_187) | ~v1_partfun1('#skF_5', A_187) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_856])).
% 3.57/1.69  tff(c_1029, plain, (![A_214, B_215]: (~v1_partfun1('#skF_6', A_214) | ~v1_partfun1('#skF_5', A_214) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(splitLeft, [status(thm)], [c_859])).
% 3.57/1.69  tff(c_1038, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_631, c_1029])).
% 3.57/1.69  tff(c_1044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_636, c_635, c_631, c_849, c_852, c_1038])).
% 3.57/1.69  tff(c_1045, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_859])).
% 3.57/1.69  tff(c_67, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_59])).
% 3.57/1.69  tff(c_633, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_631, c_67])).
% 3.57/1.69  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.57/1.69  tff(c_647, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_633, c_12])).
% 3.57/1.69  tff(c_660, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_647])).
% 3.57/1.69  tff(c_1050, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_660])).
% 3.57/1.69  tff(c_1061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_1050])).
% 3.57/1.69  tff(c_1062, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_647])).
% 3.57/1.69  tff(c_1066, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1062, c_32])).
% 3.57/1.69  tff(c_1210, plain, (![A_263, B_264, C_265, D_266]: (r2_relset_1(A_263, B_264, C_265, C_265) | ~m1_subset_1(D_266, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.69  tff(c_1212, plain, (![C_265, D_266]: (r2_relset_1('#skF_3', '#skF_4', C_265, C_265) | ~m1_subset_1(D_266, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_631, c_1210])).
% 3.57/1.69  tff(c_1216, plain, (![C_265, D_266]: (r2_relset_1('#skF_3', '#skF_4', C_265, C_265) | ~m1_subset_1(D_266, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(C_265, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_631, c_1212])).
% 3.57/1.69  tff(c_1218, plain, (![D_266]: (~m1_subset_1(D_266, k1_zfmisc_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_1216])).
% 3.57/1.69  tff(c_1220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1218, c_635])).
% 3.57/1.69  tff(c_1222, plain, (![C_267]: (r2_relset_1('#skF_3', '#skF_4', C_267, C_267) | ~m1_subset_1(C_267, k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_1216])).
% 3.57/1.69  tff(c_1224, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_635, c_1222])).
% 3.57/1.69  tff(c_1231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1066, c_1224])).
% 3.57/1.69  tff(c_1232, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_641])).
% 3.57/1.69  tff(c_1233, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_641])).
% 3.57/1.69  tff(c_1272, plain, (![A_272, B_273]: (r2_hidden('#skF_2'(A_272, B_273), A_272) | r1_tarski(A_272, B_273))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.57/1.69  tff(c_1276, plain, (![A_272, B_273]: (~v1_xboole_0(A_272) | r1_tarski(A_272, B_273))), inference(resolution, [status(thm)], [c_1272, c_2])).
% 3.57/1.69  tff(c_1277, plain, (![A_274, B_275]: (~v1_xboole_0(A_274) | r1_tarski(A_274, B_275))), inference(resolution, [status(thm)], [c_1272, c_2])).
% 3.57/1.69  tff(c_1281, plain, (![B_276, A_277]: (B_276=A_277 | ~r1_tarski(B_276, A_277) | ~v1_xboole_0(A_277))), inference(resolution, [status(thm)], [c_1277, c_12])).
% 3.57/1.69  tff(c_1291, plain, (![B_278, A_279]: (B_278=A_279 | ~v1_xboole_0(B_278) | ~v1_xboole_0(A_279))), inference(resolution, [status(thm)], [c_1276, c_1281])).
% 3.57/1.69  tff(c_1301, plain, (![A_280]: (A_280='#skF_4' | ~v1_xboole_0(A_280))), inference(resolution, [status(thm)], [c_1233, c_1291])).
% 3.57/1.69  tff(c_1313, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_1232, c_1301])).
% 3.57/1.69  tff(c_1319, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_1313, c_635])).
% 3.57/1.69  tff(c_1354, plain, (![A_283, B_284]: (k2_zfmisc_1(A_283, B_284)='#skF_4' | ~v1_xboole_0(B_284))), inference(resolution, [status(thm)], [c_18, c_1301])).
% 3.57/1.69  tff(c_1359, plain, (![A_283]: (k2_zfmisc_1(A_283, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_1233, c_1354])).
% 3.57/1.69  tff(c_1452, plain, (![A_306, B_307, C_308, D_309]: (r2_relset_1(A_306, B_307, C_308, C_308) | ~m1_subset_1(D_309, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.69  tff(c_1456, plain, (![A_283, C_308, D_309]: (r2_relset_1(A_283, '#skF_4', C_308, C_308) | ~m1_subset_1(D_309, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_283, '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_1359, c_1452])).
% 3.57/1.69  tff(c_1460, plain, (![A_283, C_308, D_309]: (r2_relset_1(A_283, '#skF_4', C_308, C_308) | ~m1_subset_1(D_309, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_308, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_1456])).
% 3.57/1.69  tff(c_1497, plain, (![D_309]: (~m1_subset_1(D_309, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_1460])).
% 3.57/1.69  tff(c_1506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1497, c_1319])).
% 3.57/1.69  tff(c_1508, plain, (![A_328, C_329]: (r2_relset_1(A_328, '#skF_4', C_329, C_329) | ~m1_subset_1(C_329, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_1460])).
% 3.57/1.69  tff(c_1514, plain, (![A_328]: (r2_relset_1(A_328, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_1319, c_1508])).
% 3.57/1.69  tff(c_1237, plain, (![A_268, B_269]: (r2_hidden('#skF_2'(A_268, B_269), A_268) | r1_tarski(A_268, B_269))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.57/1.69  tff(c_1242, plain, (![A_270, B_271]: (~v1_xboole_0(A_270) | r1_tarski(A_270, B_271))), inference(resolution, [status(thm)], [c_1237, c_2])).
% 3.57/1.69  tff(c_80, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_67, c_73])).
% 3.57/1.69  tff(c_1234, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_631, c_631, c_80])).
% 3.57/1.69  tff(c_1235, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1234])).
% 3.57/1.69  tff(c_1245, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1242, c_1235])).
% 3.57/1.69  tff(c_1251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1232, c_1245])).
% 3.57/1.69  tff(c_1252, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1234])).
% 3.57/1.69  tff(c_1256, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1252, c_32])).
% 3.57/1.69  tff(c_1315, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_1313, c_1256])).
% 3.57/1.69  tff(c_1518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1514, c_1315])).
% 3.57/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.69  
% 3.57/1.69  Inference rules
% 3.57/1.69  ----------------------
% 3.57/1.69  #Ref     : 0
% 3.57/1.69  #Sup     : 326
% 3.57/1.69  #Fact    : 0
% 3.57/1.69  #Define  : 0
% 3.57/1.69  #Split   : 14
% 3.57/1.69  #Chain   : 0
% 3.57/1.69  #Close   : 0
% 3.57/1.69  
% 3.57/1.69  Ordering : KBO
% 3.57/1.69  
% 3.57/1.69  Simplification rules
% 3.57/1.69  ----------------------
% 3.57/1.69  #Subsume      : 101
% 3.57/1.69  #Demod        : 175
% 3.57/1.69  #Tautology    : 95
% 3.57/1.69  #SimpNegUnit  : 15
% 3.57/1.69  #BackRed      : 49
% 3.57/1.69  
% 3.57/1.69  #Partial instantiations: 0
% 3.57/1.69  #Strategies tried      : 1
% 3.57/1.69  
% 3.57/1.69  Timing (in seconds)
% 3.57/1.69  ----------------------
% 3.57/1.70  Preprocessing        : 0.28
% 3.57/1.70  Parsing              : 0.15
% 3.57/1.70  CNF conversion       : 0.02
% 3.57/1.70  Main loop            : 0.59
% 3.57/1.70  Inferencing          : 0.21
% 3.57/1.70  Reduction            : 0.17
% 3.57/1.70  Demodulation         : 0.12
% 3.57/1.70  BG Simplification    : 0.02
% 3.57/1.70  Subsumption          : 0.14
% 3.57/1.70  Abstraction          : 0.02
% 3.57/1.70  MUC search           : 0.00
% 3.57/1.70  Cooper               : 0.00
% 3.57/1.70  Total                : 0.92
% 3.57/1.70  Index Insertion      : 0.00
% 3.93/1.70  Index Deletion       : 0.00
% 3.93/1.70  Index Matching       : 0.00
% 3.93/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
