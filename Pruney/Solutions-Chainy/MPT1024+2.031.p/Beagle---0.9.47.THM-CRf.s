%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:26 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 424 expanded)
%              Number of leaves         :   38 ( 160 expanded)
%              Depth                    :   13
%              Number of atoms          :  225 (1151 expanded)
%              Number of equality atoms :   56 ( 245 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_789,plain,(
    ! [A_213,B_214,C_215,D_216] :
      ( k7_relset_1(A_213,B_214,C_215,D_216) = k9_relat_1(C_215,D_216)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_799,plain,(
    ! [D_217] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_217) = k9_relat_1('#skF_5',D_217) ),
    inference(resolution,[status(thm)],[c_50,c_789])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26,D_27] :
      ( m1_subset_1(k7_relset_1(A_24,B_25,C_26,D_27),k1_zfmisc_1(B_25))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_805,plain,(
    ! [D_217] :
      ( m1_subset_1(k9_relat_1('#skF_5',D_217),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_28])).

tff(c_823,plain,(
    ! [D_220] : m1_subset_1(k9_relat_1('#skF_5',D_220),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_805])).

tff(c_8,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_829,plain,(
    ! [A_7,D_220] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_7,k9_relat_1('#skF_5',D_220)) ) ),
    inference(resolution,[status(thm)],[c_823,c_8])).

tff(c_830,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_829])).

tff(c_61,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_65,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_61])).

tff(c_796,plain,(
    ! [D_216] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_216) = k9_relat_1('#skF_5',D_216) ),
    inference(resolution,[status(thm)],[c_50,c_789])).

tff(c_48,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_798,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_48])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_1'(A_10,B_11,C_12),B_11)
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_900,plain,(
    ! [A_234,B_235,C_236] :
      ( r2_hidden(k4_tarski('#skF_1'(A_234,B_235,C_236),A_234),C_236)
      | ~ r2_hidden(A_234,k9_relat_1(C_236,B_235))
      | ~ v1_relat_1(C_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [C_18,A_16,B_17] :
      ( k1_funct_1(C_18,A_16) = B_17
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1062,plain,(
    ! [C_268,A_269,B_270] :
      ( k1_funct_1(C_268,'#skF_1'(A_269,B_270,C_268)) = A_269
      | ~ v1_funct_1(C_268)
      | ~ r2_hidden(A_269,k9_relat_1(C_268,B_270))
      | ~ v1_relat_1(C_268) ) ),
    inference(resolution,[status(thm)],[c_900,c_20])).

tff(c_1070,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_798,c_1062])).

tff(c_1081,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54,c_1070])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_696,plain,(
    ! [A_181,B_182,C_183] :
      ( k1_relset_1(A_181,B_182,C_183) = k1_relat_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_700,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_696])).

tff(c_1242,plain,(
    ! [B_282,A_283,C_284] :
      ( k1_xboole_0 = B_282
      | k1_relset_1(A_283,B_282,C_284) = A_283
      | ~ v1_funct_2(C_284,A_283,B_282)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_283,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1249,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1242])).

tff(c_1253,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_700,c_1249])).

tff(c_1254,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1253])).

tff(c_1099,plain,(
    ! [B_271,A_272,C_273] :
      ( k1_xboole_0 = B_271
      | k1_relset_1(A_272,B_271,C_273) = A_272
      | ~ v1_funct_2(C_273,A_272,B_271)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_272,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1106,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1099])).

tff(c_1110,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_700,c_1106])).

tff(c_1111,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1110])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_1'(A_10,B_11,C_12),k1_relat_1(C_12))
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1119,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_1'(A_10,B_11,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_10,k9_relat_1('#skF_5',B_11))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_16])).

tff(c_1182,plain,(
    ! [A_280,B_281] :
      ( r2_hidden('#skF_1'(A_280,B_281,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_280,k9_relat_1('#skF_5',B_281)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1119])).

tff(c_861,plain,(
    ! [A_232,C_233] :
      ( r2_hidden(k4_tarski(A_232,k1_funct_1(C_233,A_232)),C_233)
      | ~ r2_hidden(A_232,k1_relat_1(C_233))
      | ~ v1_funct_1(C_233)
      | ~ v1_relat_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_899,plain,(
    ! [C_233,A_232] :
      ( ~ r1_tarski(C_233,k4_tarski(A_232,k1_funct_1(C_233,A_232)))
      | ~ r2_hidden(A_232,k1_relat_1(C_233))
      | ~ v1_funct_1(C_233)
      | ~ v1_relat_1(C_233) ) ),
    inference(resolution,[status(thm)],[c_861,c_24])).

tff(c_1087,plain,
    ( ~ r1_tarski('#skF_5',k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'))
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_899])).

tff(c_1094,plain,
    ( ~ r1_tarski('#skF_5',k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'))
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54,c_1087])).

tff(c_1098,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1094])).

tff(c_1132,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1111,c_1098])).

tff(c_1187,plain,(
    ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1182,c_1132])).

tff(c_1198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_798,c_1187])).

tff(c_1199,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1110])).

tff(c_178,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k7_relset_1(A_92,B_93,C_94,D_95) = k9_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_181,plain,(
    ! [D_95] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_95) = k9_relat_1('#skF_5',D_95) ),
    inference(resolution,[status(thm)],[c_50,c_178])).

tff(c_183,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_48])).

tff(c_285,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden(k4_tarski('#skF_1'(A_117,B_118,C_119),A_117),C_119)
      | ~ r2_hidden(A_117,k9_relat_1(C_119,B_118))
      | ~ v1_relat_1(C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_548,plain,(
    ! [C_162,A_163,B_164] :
      ( k1_funct_1(C_162,'#skF_1'(A_163,B_164,C_162)) = A_163
      | ~ v1_funct_1(C_162)
      | ~ r2_hidden(A_163,k9_relat_1(C_162,B_164))
      | ~ v1_relat_1(C_162) ) ),
    inference(resolution,[status(thm)],[c_285,c_20])).

tff(c_556,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_183,c_548])).

tff(c_567,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54,c_556])).

tff(c_101,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_105,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_101])).

tff(c_436,plain,(
    ! [B_138,A_139,C_140] :
      ( k1_xboole_0 = B_138
      | k1_relset_1(A_139,B_138,C_140) = A_139
      | ~ v1_funct_2(C_140,A_139,B_138)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_443,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_436])).

tff(c_447,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_105,c_443])).

tff(c_448,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_456,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_1'(A_10,B_11,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_10,k9_relat_1('#skF_5',B_11))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_16])).

tff(c_493,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_1'(A_143,B_144,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_143,k9_relat_1('#skF_5',B_144)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_456])).

tff(c_46,plain,(
    ! [F_42] :
      ( k1_funct_1('#skF_5',F_42) != '#skF_6'
      | ~ r2_hidden(F_42,'#skF_4')
      | ~ r2_hidden(F_42,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_570,plain,(
    ! [A_165,B_166] :
      ( k1_funct_1('#skF_5','#skF_1'(A_165,B_166,'#skF_5')) != '#skF_6'
      | ~ r2_hidden('#skF_1'(A_165,B_166,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_165,k9_relat_1('#skF_5',B_166)) ) ),
    inference(resolution,[status(thm)],[c_493,c_46])).

tff(c_574,plain,(
    ! [A_10] :
      ( k1_funct_1('#skF_5','#skF_1'(A_10,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_10,k9_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_570])).

tff(c_596,plain,(
    ! [A_167] :
      ( k1_funct_1('#skF_5','#skF_1'(A_167,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_167,k9_relat_1('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_574])).

tff(c_607,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_183,c_596])).

tff(c_621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_607])).

tff(c_622,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,B_51)
      | v1_xboole_0(B_51)
      | ~ m1_subset_1(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [B_52,A_53] :
      ( ~ r1_tarski(B_52,A_53)
      | v1_xboole_0(B_52)
      | ~ m1_subset_1(A_53,B_52) ) ),
    inference(resolution,[status(thm)],[c_67,c_24])).

tff(c_81,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_82,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_634,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_82])).

tff(c_199,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( m1_subset_1(k7_relset_1(A_99,B_100,C_101,D_102),k1_zfmisc_1(B_100))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_221,plain,(
    ! [D_95] :
      ( m1_subset_1(k9_relat_1('#skF_5',D_95),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_199])).

tff(c_230,plain,(
    ! [D_103] : m1_subset_1(k9_relat_1('#skF_5',D_103),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_221])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( m1_subset_1(A_4,C_6)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(C_6))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_244,plain,(
    ! [A_106,D_107] :
      ( m1_subset_1(A_106,'#skF_3')
      | ~ r2_hidden(A_106,k9_relat_1('#skF_5',D_107)) ) ),
    inference(resolution,[status(thm)],[c_230,c_6])).

tff(c_256,plain,(
    m1_subset_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_183,c_244])).

tff(c_676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_634,c_256])).

tff(c_677,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_1213,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_677])).

tff(c_1216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_830,c_1213])).

tff(c_1218,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1094])).

tff(c_1256,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1254,c_1218])).

tff(c_1278,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1256,c_46])).

tff(c_1284,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_1278])).

tff(c_1288,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_1284])).

tff(c_1295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_798,c_1288])).

tff(c_1296,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1253])).

tff(c_1310,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_677])).

tff(c_1313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_830,c_1310])).

tff(c_1314,plain,(
    ! [A_7,D_220] : ~ r2_hidden(A_7,k9_relat_1('#skF_5',D_220)) ),
    inference(splitRight,[status(thm)],[c_829])).

tff(c_1323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1314,c_798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.64  
% 3.74/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.65  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.74/1.65  
% 3.74/1.65  %Foreground sorts:
% 3.74/1.65  
% 3.74/1.65  
% 3.74/1.65  %Background operators:
% 3.74/1.65  
% 3.74/1.65  
% 3.74/1.65  %Foreground operators:
% 3.74/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.74/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.74/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.74/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.65  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.74/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.74/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.74/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.74/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.74/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.74/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.74/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.74/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.74/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.74/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.74/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.65  
% 3.74/1.67  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 3.74/1.67  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.74/1.67  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.74/1.67  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.74/1.67  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.74/1.67  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.74/1.67  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.74/1.67  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.74/1.67  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.74/1.67  tff(f_72, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.74/1.67  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.74/1.67  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.74/1.67  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.74/1.67  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.74/1.67  tff(c_789, plain, (![A_213, B_214, C_215, D_216]: (k7_relset_1(A_213, B_214, C_215, D_216)=k9_relat_1(C_215, D_216) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.74/1.67  tff(c_799, plain, (![D_217]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_217)=k9_relat_1('#skF_5', D_217))), inference(resolution, [status(thm)], [c_50, c_789])).
% 3.74/1.67  tff(c_28, plain, (![A_24, B_25, C_26, D_27]: (m1_subset_1(k7_relset_1(A_24, B_25, C_26, D_27), k1_zfmisc_1(B_25)) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.74/1.67  tff(c_805, plain, (![D_217]: (m1_subset_1(k9_relat_1('#skF_5', D_217), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_799, c_28])).
% 3.74/1.67  tff(c_823, plain, (![D_220]: (m1_subset_1(k9_relat_1('#skF_5', D_220), k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_805])).
% 3.74/1.67  tff(c_8, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.74/1.67  tff(c_829, plain, (![A_7, D_220]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_7, k9_relat_1('#skF_5', D_220)))), inference(resolution, [status(thm)], [c_823, c_8])).
% 3.74/1.67  tff(c_830, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_829])).
% 3.74/1.67  tff(c_61, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.74/1.67  tff(c_65, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_61])).
% 3.74/1.67  tff(c_796, plain, (![D_216]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_216)=k9_relat_1('#skF_5', D_216))), inference(resolution, [status(thm)], [c_50, c_789])).
% 3.74/1.67  tff(c_48, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.74/1.67  tff(c_798, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_796, c_48])).
% 3.74/1.67  tff(c_12, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_1'(A_10, B_11, C_12), B_11) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.74/1.67  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.74/1.67  tff(c_900, plain, (![A_234, B_235, C_236]: (r2_hidden(k4_tarski('#skF_1'(A_234, B_235, C_236), A_234), C_236) | ~r2_hidden(A_234, k9_relat_1(C_236, B_235)) | ~v1_relat_1(C_236))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.74/1.67  tff(c_20, plain, (![C_18, A_16, B_17]: (k1_funct_1(C_18, A_16)=B_17 | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.74/1.67  tff(c_1062, plain, (![C_268, A_269, B_270]: (k1_funct_1(C_268, '#skF_1'(A_269, B_270, C_268))=A_269 | ~v1_funct_1(C_268) | ~r2_hidden(A_269, k9_relat_1(C_268, B_270)) | ~v1_relat_1(C_268))), inference(resolution, [status(thm)], [c_900, c_20])).
% 3.74/1.67  tff(c_1070, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_798, c_1062])).
% 3.74/1.67  tff(c_1081, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54, c_1070])).
% 3.74/1.67  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.74/1.67  tff(c_696, plain, (![A_181, B_182, C_183]: (k1_relset_1(A_181, B_182, C_183)=k1_relat_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.74/1.67  tff(c_700, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_696])).
% 3.74/1.67  tff(c_1242, plain, (![B_282, A_283, C_284]: (k1_xboole_0=B_282 | k1_relset_1(A_283, B_282, C_284)=A_283 | ~v1_funct_2(C_284, A_283, B_282) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_283, B_282))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.74/1.67  tff(c_1249, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1242])).
% 3.74/1.67  tff(c_1253, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_700, c_1249])).
% 3.74/1.67  tff(c_1254, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_1253])).
% 3.74/1.67  tff(c_1099, plain, (![B_271, A_272, C_273]: (k1_xboole_0=B_271 | k1_relset_1(A_272, B_271, C_273)=A_272 | ~v1_funct_2(C_273, A_272, B_271) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_272, B_271))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.74/1.67  tff(c_1106, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1099])).
% 3.74/1.67  tff(c_1110, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_700, c_1106])).
% 3.74/1.67  tff(c_1111, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_1110])).
% 3.74/1.67  tff(c_16, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_1'(A_10, B_11, C_12), k1_relat_1(C_12)) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.74/1.67  tff(c_1119, plain, (![A_10, B_11]: (r2_hidden('#skF_1'(A_10, B_11, '#skF_5'), '#skF_2') | ~r2_hidden(A_10, k9_relat_1('#skF_5', B_11)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1111, c_16])).
% 3.74/1.67  tff(c_1182, plain, (![A_280, B_281]: (r2_hidden('#skF_1'(A_280, B_281, '#skF_5'), '#skF_2') | ~r2_hidden(A_280, k9_relat_1('#skF_5', B_281)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_1119])).
% 3.74/1.67  tff(c_861, plain, (![A_232, C_233]: (r2_hidden(k4_tarski(A_232, k1_funct_1(C_233, A_232)), C_233) | ~r2_hidden(A_232, k1_relat_1(C_233)) | ~v1_funct_1(C_233) | ~v1_relat_1(C_233))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.74/1.67  tff(c_24, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.74/1.67  tff(c_899, plain, (![C_233, A_232]: (~r1_tarski(C_233, k4_tarski(A_232, k1_funct_1(C_233, A_232))) | ~r2_hidden(A_232, k1_relat_1(C_233)) | ~v1_funct_1(C_233) | ~v1_relat_1(C_233))), inference(resolution, [status(thm)], [c_861, c_24])).
% 3.74/1.67  tff(c_1087, plain, (~r1_tarski('#skF_5', k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6')) | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1081, c_899])).
% 3.74/1.67  tff(c_1094, plain, (~r1_tarski('#skF_5', k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6')) | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54, c_1087])).
% 3.74/1.67  tff(c_1098, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1094])).
% 3.74/1.67  tff(c_1132, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1111, c_1098])).
% 3.74/1.67  tff(c_1187, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_1182, c_1132])).
% 3.74/1.67  tff(c_1198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_798, c_1187])).
% 3.74/1.67  tff(c_1199, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1110])).
% 3.74/1.67  tff(c_178, plain, (![A_92, B_93, C_94, D_95]: (k7_relset_1(A_92, B_93, C_94, D_95)=k9_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.74/1.67  tff(c_181, plain, (![D_95]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_95)=k9_relat_1('#skF_5', D_95))), inference(resolution, [status(thm)], [c_50, c_178])).
% 3.74/1.67  tff(c_183, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_48])).
% 3.74/1.67  tff(c_285, plain, (![A_117, B_118, C_119]: (r2_hidden(k4_tarski('#skF_1'(A_117, B_118, C_119), A_117), C_119) | ~r2_hidden(A_117, k9_relat_1(C_119, B_118)) | ~v1_relat_1(C_119))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.74/1.67  tff(c_548, plain, (![C_162, A_163, B_164]: (k1_funct_1(C_162, '#skF_1'(A_163, B_164, C_162))=A_163 | ~v1_funct_1(C_162) | ~r2_hidden(A_163, k9_relat_1(C_162, B_164)) | ~v1_relat_1(C_162))), inference(resolution, [status(thm)], [c_285, c_20])).
% 3.74/1.67  tff(c_556, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_183, c_548])).
% 3.74/1.67  tff(c_567, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54, c_556])).
% 3.74/1.67  tff(c_101, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.74/1.67  tff(c_105, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_101])).
% 3.74/1.67  tff(c_436, plain, (![B_138, A_139, C_140]: (k1_xboole_0=B_138 | k1_relset_1(A_139, B_138, C_140)=A_139 | ~v1_funct_2(C_140, A_139, B_138) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.74/1.67  tff(c_443, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_436])).
% 3.74/1.67  tff(c_447, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_105, c_443])).
% 3.74/1.67  tff(c_448, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_447])).
% 3.74/1.67  tff(c_456, plain, (![A_10, B_11]: (r2_hidden('#skF_1'(A_10, B_11, '#skF_5'), '#skF_2') | ~r2_hidden(A_10, k9_relat_1('#skF_5', B_11)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_448, c_16])).
% 3.74/1.67  tff(c_493, plain, (![A_143, B_144]: (r2_hidden('#skF_1'(A_143, B_144, '#skF_5'), '#skF_2') | ~r2_hidden(A_143, k9_relat_1('#skF_5', B_144)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_456])).
% 3.74/1.67  tff(c_46, plain, (![F_42]: (k1_funct_1('#skF_5', F_42)!='#skF_6' | ~r2_hidden(F_42, '#skF_4') | ~r2_hidden(F_42, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.74/1.67  tff(c_570, plain, (![A_165, B_166]: (k1_funct_1('#skF_5', '#skF_1'(A_165, B_166, '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'(A_165, B_166, '#skF_5'), '#skF_4') | ~r2_hidden(A_165, k9_relat_1('#skF_5', B_166)))), inference(resolution, [status(thm)], [c_493, c_46])).
% 3.74/1.67  tff(c_574, plain, (![A_10]: (k1_funct_1('#skF_5', '#skF_1'(A_10, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_10, k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_570])).
% 3.74/1.67  tff(c_596, plain, (![A_167]: (k1_funct_1('#skF_5', '#skF_1'(A_167, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_167, k9_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_574])).
% 3.74/1.67  tff(c_607, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(resolution, [status(thm)], [c_183, c_596])).
% 3.74/1.67  tff(c_621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_567, c_607])).
% 3.74/1.67  tff(c_622, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_447])).
% 3.74/1.67  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.74/1.67  tff(c_67, plain, (![A_50, B_51]: (r2_hidden(A_50, B_51) | v1_xboole_0(B_51) | ~m1_subset_1(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.67  tff(c_77, plain, (![B_52, A_53]: (~r1_tarski(B_52, A_53) | v1_xboole_0(B_52) | ~m1_subset_1(A_53, B_52))), inference(resolution, [status(thm)], [c_67, c_24])).
% 3.74/1.67  tff(c_81, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_77])).
% 3.74/1.67  tff(c_82, plain, (![A_1]: (~m1_subset_1(A_1, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_81])).
% 3.74/1.67  tff(c_634, plain, (![A_1]: (~m1_subset_1(A_1, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_82])).
% 3.74/1.67  tff(c_199, plain, (![A_99, B_100, C_101, D_102]: (m1_subset_1(k7_relset_1(A_99, B_100, C_101, D_102), k1_zfmisc_1(B_100)) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.74/1.67  tff(c_221, plain, (![D_95]: (m1_subset_1(k9_relat_1('#skF_5', D_95), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_181, c_199])).
% 3.74/1.67  tff(c_230, plain, (![D_103]: (m1_subset_1(k9_relat_1('#skF_5', D_103), k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_221])).
% 3.74/1.67  tff(c_6, plain, (![A_4, C_6, B_5]: (m1_subset_1(A_4, C_6) | ~m1_subset_1(B_5, k1_zfmisc_1(C_6)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.74/1.67  tff(c_244, plain, (![A_106, D_107]: (m1_subset_1(A_106, '#skF_3') | ~r2_hidden(A_106, k9_relat_1('#skF_5', D_107)))), inference(resolution, [status(thm)], [c_230, c_6])).
% 3.74/1.67  tff(c_256, plain, (m1_subset_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_183, c_244])).
% 3.74/1.67  tff(c_676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_634, c_256])).
% 3.74/1.67  tff(c_677, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_81])).
% 3.74/1.67  tff(c_1213, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_677])).
% 3.74/1.67  tff(c_1216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_830, c_1213])).
% 3.74/1.67  tff(c_1218, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1094])).
% 3.74/1.67  tff(c_1256, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1254, c_1218])).
% 3.74/1.67  tff(c_1278, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1256, c_46])).
% 3.74/1.67  tff(c_1284, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_1278])).
% 3.74/1.67  tff(c_1288, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_1284])).
% 3.74/1.67  tff(c_1295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_798, c_1288])).
% 3.74/1.67  tff(c_1296, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1253])).
% 3.74/1.67  tff(c_1310, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_677])).
% 3.74/1.67  tff(c_1313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_830, c_1310])).
% 3.74/1.67  tff(c_1314, plain, (![A_7, D_220]: (~r2_hidden(A_7, k9_relat_1('#skF_5', D_220)))), inference(splitRight, [status(thm)], [c_829])).
% 3.74/1.67  tff(c_1323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1314, c_798])).
% 3.74/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.67  
% 3.74/1.67  Inference rules
% 3.74/1.67  ----------------------
% 3.74/1.67  #Ref     : 0
% 3.74/1.67  #Sup     : 247
% 3.74/1.67  #Fact    : 0
% 3.74/1.67  #Define  : 0
% 3.74/1.67  #Split   : 23
% 3.74/1.67  #Chain   : 0
% 3.74/1.67  #Close   : 0
% 3.74/1.67  
% 3.74/1.67  Ordering : KBO
% 3.74/1.67  
% 3.74/1.67  Simplification rules
% 3.74/1.67  ----------------------
% 3.74/1.67  #Subsume      : 17
% 3.74/1.67  #Demod        : 147
% 3.74/1.67  #Tautology    : 34
% 3.74/1.67  #SimpNegUnit  : 11
% 3.74/1.67  #BackRed      : 53
% 3.74/1.67  
% 3.74/1.67  #Partial instantiations: 0
% 3.74/1.67  #Strategies tried      : 1
% 3.74/1.67  
% 3.74/1.67  Timing (in seconds)
% 3.74/1.67  ----------------------
% 3.74/1.67  Preprocessing        : 0.34
% 3.74/1.67  Parsing              : 0.18
% 3.74/1.67  CNF conversion       : 0.02
% 3.74/1.67  Main loop            : 0.54
% 3.74/1.67  Inferencing          : 0.20
% 3.74/1.67  Reduction            : 0.15
% 3.74/1.67  Demodulation         : 0.11
% 3.74/1.67  BG Simplification    : 0.03
% 3.74/1.67  Subsumption          : 0.11
% 3.74/1.67  Abstraction          : 0.03
% 3.74/1.67  MUC search           : 0.00
% 3.74/1.67  Cooper               : 0.00
% 3.74/1.67  Total                : 0.93
% 3.74/1.67  Index Insertion      : 0.00
% 3.74/1.67  Index Deletion       : 0.00
% 3.74/1.67  Index Matching       : 0.00
% 3.74/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
