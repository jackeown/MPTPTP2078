%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:14 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.42s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 903 expanded)
%              Number of leaves         :   45 ( 321 expanded)
%              Depth                    :   11
%              Number of atoms          :  239 (2353 expanded)
%              Number of equality atoms :   56 ( 334 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_104,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_143,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_54,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_126,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_46,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_22,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_70,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_1234,plain,(
    ! [A_268,F_269,B_267,C_271,E_270,D_266] :
      ( m1_subset_1(k1_partfun1(A_268,B_267,C_271,D_266,E_270,F_269),k1_zfmisc_1(k2_zfmisc_1(A_268,D_266)))
      | ~ m1_subset_1(F_269,k1_zfmisc_1(k2_zfmisc_1(C_271,D_266)))
      | ~ v1_funct_1(F_269)
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_267)))
      | ~ v1_funct_1(E_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_69,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_36])).

tff(c_56,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1094,plain,(
    ! [D_236,C_237,A_238,B_239] :
      ( D_236 = C_237
      | ~ r2_relset_1(A_238,B_239,C_237,D_236)
      | ~ m1_subset_1(D_236,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1104,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_56,c_1094])).

tff(c_1123,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1104])).

tff(c_1140,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1123])).

tff(c_1240,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1234,c_1140])).

tff(c_1269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_1240])).

tff(c_1270,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_1611,plain,(
    ! [C_349,D_350,A_348,E_347,B_351] :
      ( k1_xboole_0 = C_349
      | v2_funct_1(D_350)
      | ~ v2_funct_1(k1_partfun1(A_348,B_351,B_351,C_349,D_350,E_347))
      | ~ m1_subset_1(E_347,k1_zfmisc_1(k2_zfmisc_1(B_351,C_349)))
      | ~ v1_funct_2(E_347,B_351,C_349)
      | ~ v1_funct_1(E_347)
      | ~ m1_subset_1(D_350,k1_zfmisc_1(k2_zfmisc_1(A_348,B_351)))
      | ~ v1_funct_2(D_350,A_348,B_351)
      | ~ v1_funct_1(D_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1613,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_1611])).

tff(c_1615,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_58,c_70,c_1613])).

tff(c_1616,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_1615])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1651,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1649,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_1616,c_12])).

tff(c_214,plain,(
    ! [C_69,B_70,A_71] :
      ( ~ v1_xboole_0(C_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(C_69))
      | ~ r2_hidden(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_71,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_214])).

tff(c_270,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_1799,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_270])).

tff(c_1803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1651,c_1799])).

tff(c_1806,plain,(
    ! [A_372] : ~ r2_hidden(A_372,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_1811,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_1806])).

tff(c_128,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_131,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_1817,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1811,c_131])).

tff(c_1805,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_1824,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1805,c_131])).

tff(c_1890,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1817,c_1824])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2137,plain,(
    ! [B_405,A_406] :
      ( B_405 = '#skF_5'
      | A_406 = '#skF_5'
      | k2_zfmisc_1(A_406,B_405) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1817,c_1817,c_1817,c_10])).

tff(c_2151,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1890,c_2137])).

tff(c_2152,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2151])).

tff(c_2172,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_1811])).

tff(c_1837,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1817,c_1817,c_12])).

tff(c_2165,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_2152,c_1837])).

tff(c_227,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_71,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_214])).

tff(c_236,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_2350,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2165,c_236])).

tff(c_2354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2172,c_2350])).

tff(c_2355,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2151])).

tff(c_2376,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2355,c_1811])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1836,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_5',B_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1817,c_1817,c_14])).

tff(c_2366,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_2',B_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2355,c_2355,c_1836])).

tff(c_2554,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2366,c_236])).

tff(c_2558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2376,c_2554])).

tff(c_2561,plain,(
    ! [A_445] : ~ r2_hidden(A_445,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_2566,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_2561])).

tff(c_2572,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2566,c_131])).

tff(c_102,plain,(
    ! [A_52] : k6_relat_1(A_52) = k6_partfun1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_108,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_121,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_70])).

tff(c_2579,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2572,c_121])).

tff(c_2587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_2579])).

tff(c_2588,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2634,plain,(
    ! [C_455,A_456,B_457] :
      ( v1_relat_1(C_455)
      | ~ m1_subset_1(C_455,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2650,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2634])).

tff(c_2673,plain,(
    ! [C_462,B_463,A_464] :
      ( v5_relat_1(C_462,B_463)
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(A_464,B_463))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2690,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2673])).

tff(c_2759,plain,(
    ! [A_480,B_481,D_482] :
      ( r2_relset_1(A_480,B_481,D_482,D_482)
      | ~ m1_subset_1(D_482,k1_zfmisc_1(k2_zfmisc_1(A_480,B_481))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2770,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_69,c_2759])).

tff(c_2815,plain,(
    ! [A_487,B_488,C_489] :
      ( k2_relset_1(A_487,B_488,C_489) = k2_relat_1(C_489)
      | ~ m1_subset_1(C_489,k1_zfmisc_1(k2_zfmisc_1(A_487,B_488))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2832,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2815])).

tff(c_3004,plain,(
    ! [D_522,E_526,F_525,C_527,B_523,A_524] :
      ( m1_subset_1(k1_partfun1(A_524,B_523,C_527,D_522,E_526,F_525),k1_zfmisc_1(k2_zfmisc_1(A_524,D_522)))
      | ~ m1_subset_1(F_525,k1_zfmisc_1(k2_zfmisc_1(C_527,D_522)))
      | ~ v1_funct_1(F_525)
      | ~ m1_subset_1(E_526,k1_zfmisc_1(k2_zfmisc_1(A_524,B_523)))
      | ~ v1_funct_1(E_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2864,plain,(
    ! [D_492,C_493,A_494,B_495] :
      ( D_492 = C_493
      | ~ r2_relset_1(A_494,B_495,C_493,D_492)
      | ~ m1_subset_1(D_492,k1_zfmisc_1(k2_zfmisc_1(A_494,B_495)))
      | ~ m1_subset_1(C_493,k1_zfmisc_1(k2_zfmisc_1(A_494,B_495))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2874,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_56,c_2864])).

tff(c_2893,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2874])).

tff(c_2910,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2893])).

tff(c_3010,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3004,c_2910])).

tff(c_3039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_3010])).

tff(c_3040,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2893])).

tff(c_3367,plain,(
    ! [A_614,B_615,C_616,D_617] :
      ( k2_relset_1(A_614,B_615,C_616) = B_615
      | ~ r2_relset_1(B_615,B_615,k1_partfun1(B_615,A_614,A_614,B_615,D_617,C_616),k6_partfun1(B_615))
      | ~ m1_subset_1(D_617,k1_zfmisc_1(k2_zfmisc_1(B_615,A_614)))
      | ~ v1_funct_2(D_617,B_615,A_614)
      | ~ v1_funct_1(D_617)
      | ~ m1_subset_1(C_616,k1_zfmisc_1(k2_zfmisc_1(A_614,B_615)))
      | ~ v1_funct_2(C_616,A_614,B_615)
      | ~ v1_funct_1(C_616) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3370,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3040,c_3367])).

tff(c_3375,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_68,c_66,c_64,c_2770,c_2832,c_3370])).

tff(c_38,plain,(
    ! [B_28] :
      ( v2_funct_2(B_28,k2_relat_1(B_28))
      | ~ v5_relat_1(B_28,k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3381,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3375,c_38])).

tff(c_3385,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2650,c_2690,c_3375,c_3381])).

tff(c_3387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2588,c_3385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.00  
% 5.42/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.00  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.42/2.00  
% 5.42/2.00  %Foreground sorts:
% 5.42/2.00  
% 5.42/2.00  
% 5.42/2.00  %Background operators:
% 5.42/2.00  
% 5.42/2.00  
% 5.42/2.00  %Foreground operators:
% 5.42/2.00  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.42/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.42/2.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.42/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.42/2.00  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.42/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.42/2.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.42/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.42/2.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.42/2.00  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.42/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.42/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.42/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.42/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.42/2.00  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.42/2.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.42/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.42/2.00  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.42/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.42/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.42/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.42/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.42/2.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.42/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.42/2.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.42/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.42/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.42/2.00  
% 5.42/2.02  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.42/2.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.42/2.02  tff(f_104, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.42/2.02  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.42/2.02  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.42/2.02  tff(f_82, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.42/2.02  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.42/2.02  tff(f_143, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.42/2.02  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.42/2.02  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.42/2.02  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.42/2.02  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 5.42/2.02  tff(f_54, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 5.42/2.02  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.42/2.02  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.42/2.02  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.42/2.02  tff(f_121, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.42/2.02  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.42/2.02  tff(c_54, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.42/2.02  tff(c_126, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 5.42/2.02  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.42/2.02  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.42/2.02  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.42/2.02  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.42/2.02  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.42/2.02  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.42/2.02  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.42/2.02  tff(c_46, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.42/2.02  tff(c_22, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.42/2.02  tff(c_70, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_22])).
% 5.42/2.02  tff(c_1234, plain, (![A_268, F_269, B_267, C_271, E_270, D_266]: (m1_subset_1(k1_partfun1(A_268, B_267, C_271, D_266, E_270, F_269), k1_zfmisc_1(k2_zfmisc_1(A_268, D_266))) | ~m1_subset_1(F_269, k1_zfmisc_1(k2_zfmisc_1(C_271, D_266))) | ~v1_funct_1(F_269) | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_267))) | ~v1_funct_1(E_270))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.42/2.02  tff(c_36, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.42/2.02  tff(c_69, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_36])).
% 5.42/2.02  tff(c_56, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.42/2.02  tff(c_1094, plain, (![D_236, C_237, A_238, B_239]: (D_236=C_237 | ~r2_relset_1(A_238, B_239, C_237, D_236) | ~m1_subset_1(D_236, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.42/2.02  tff(c_1104, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_56, c_1094])).
% 5.42/2.02  tff(c_1123, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1104])).
% 5.42/2.02  tff(c_1140, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1123])).
% 5.42/2.02  tff(c_1240, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1234, c_1140])).
% 5.42/2.02  tff(c_1269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_1240])).
% 5.42/2.02  tff(c_1270, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1123])).
% 5.42/2.02  tff(c_1611, plain, (![C_349, D_350, A_348, E_347, B_351]: (k1_xboole_0=C_349 | v2_funct_1(D_350) | ~v2_funct_1(k1_partfun1(A_348, B_351, B_351, C_349, D_350, E_347)) | ~m1_subset_1(E_347, k1_zfmisc_1(k2_zfmisc_1(B_351, C_349))) | ~v1_funct_2(E_347, B_351, C_349) | ~v1_funct_1(E_347) | ~m1_subset_1(D_350, k1_zfmisc_1(k2_zfmisc_1(A_348, B_351))) | ~v1_funct_2(D_350, A_348, B_351) | ~v1_funct_1(D_350))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.42/2.02  tff(c_1613, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1270, c_1611])).
% 5.42/2.02  tff(c_1615, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_70, c_1613])).
% 5.42/2.02  tff(c_1616, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_126, c_1615])).
% 5.42/2.02  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.42/2.02  tff(c_1651, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_6])).
% 5.42/2.02  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.42/2.02  tff(c_1649, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_1616, c_12])).
% 5.42/2.02  tff(c_214, plain, (![C_69, B_70, A_71]: (~v1_xboole_0(C_69) | ~m1_subset_1(B_70, k1_zfmisc_1(C_69)) | ~r2_hidden(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.42/2.02  tff(c_228, plain, (![A_71]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_71, '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_214])).
% 5.42/2.02  tff(c_270, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_228])).
% 5.42/2.02  tff(c_1799, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_270])).
% 5.42/2.02  tff(c_1803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1651, c_1799])).
% 5.42/2.02  tff(c_1806, plain, (![A_372]: (~r2_hidden(A_372, '#skF_5'))), inference(splitRight, [status(thm)], [c_228])).
% 5.42/2.02  tff(c_1811, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_1806])).
% 5.42/2.02  tff(c_128, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.42/2.02  tff(c_131, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_6, c_128])).
% 5.42/2.02  tff(c_1817, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1811, c_131])).
% 5.42/2.02  tff(c_1805, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_228])).
% 5.42/2.02  tff(c_1824, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1805, c_131])).
% 5.42/2.02  tff(c_1890, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1817, c_1824])).
% 5.42/2.02  tff(c_10, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.42/2.02  tff(c_2137, plain, (![B_405, A_406]: (B_405='#skF_5' | A_406='#skF_5' | k2_zfmisc_1(A_406, B_405)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1817, c_1817, c_1817, c_10])).
% 5.42/2.02  tff(c_2151, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1890, c_2137])).
% 5.42/2.02  tff(c_2152, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_2151])).
% 5.42/2.02  tff(c_2172, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_1811])).
% 5.42/2.02  tff(c_1837, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1817, c_1817, c_12])).
% 5.42/2.02  tff(c_2165, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_2152, c_1837])).
% 5.42/2.02  tff(c_227, plain, (![A_71]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_71, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_214])).
% 5.42/2.02  tff(c_236, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_227])).
% 5.42/2.02  tff(c_2350, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2165, c_236])).
% 5.42/2.02  tff(c_2354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2172, c_2350])).
% 5.42/2.02  tff(c_2355, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_2151])).
% 5.42/2.02  tff(c_2376, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2355, c_1811])).
% 5.42/2.02  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.42/2.02  tff(c_1836, plain, (![B_8]: (k2_zfmisc_1('#skF_5', B_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1817, c_1817, c_14])).
% 5.42/2.02  tff(c_2366, plain, (![B_8]: (k2_zfmisc_1('#skF_2', B_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2355, c_2355, c_1836])).
% 5.42/2.02  tff(c_2554, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2366, c_236])).
% 5.42/2.02  tff(c_2558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2376, c_2554])).
% 5.42/2.02  tff(c_2561, plain, (![A_445]: (~r2_hidden(A_445, '#skF_4'))), inference(splitRight, [status(thm)], [c_227])).
% 5.42/2.02  tff(c_2566, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_2561])).
% 5.42/2.02  tff(c_2572, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2566, c_131])).
% 5.42/2.02  tff(c_102, plain, (![A_52]: (k6_relat_1(A_52)=k6_partfun1(A_52))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.42/2.02  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.42/2.02  tff(c_108, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_102, c_18])).
% 5.42/2.02  tff(c_121, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_70])).
% 5.42/2.02  tff(c_2579, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2572, c_121])).
% 5.42/2.02  tff(c_2587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_2579])).
% 5.42/2.02  tff(c_2588, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 5.42/2.02  tff(c_2634, plain, (![C_455, A_456, B_457]: (v1_relat_1(C_455) | ~m1_subset_1(C_455, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.42/2.02  tff(c_2650, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2634])).
% 5.42/2.02  tff(c_2673, plain, (![C_462, B_463, A_464]: (v5_relat_1(C_462, B_463) | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(A_464, B_463))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.42/2.02  tff(c_2690, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_2673])).
% 5.42/2.02  tff(c_2759, plain, (![A_480, B_481, D_482]: (r2_relset_1(A_480, B_481, D_482, D_482) | ~m1_subset_1(D_482, k1_zfmisc_1(k2_zfmisc_1(A_480, B_481))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.42/2.02  tff(c_2770, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_69, c_2759])).
% 5.42/2.02  tff(c_2815, plain, (![A_487, B_488, C_489]: (k2_relset_1(A_487, B_488, C_489)=k2_relat_1(C_489) | ~m1_subset_1(C_489, k1_zfmisc_1(k2_zfmisc_1(A_487, B_488))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.42/2.02  tff(c_2832, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2815])).
% 5.42/2.02  tff(c_3004, plain, (![D_522, E_526, F_525, C_527, B_523, A_524]: (m1_subset_1(k1_partfun1(A_524, B_523, C_527, D_522, E_526, F_525), k1_zfmisc_1(k2_zfmisc_1(A_524, D_522))) | ~m1_subset_1(F_525, k1_zfmisc_1(k2_zfmisc_1(C_527, D_522))) | ~v1_funct_1(F_525) | ~m1_subset_1(E_526, k1_zfmisc_1(k2_zfmisc_1(A_524, B_523))) | ~v1_funct_1(E_526))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.42/2.02  tff(c_2864, plain, (![D_492, C_493, A_494, B_495]: (D_492=C_493 | ~r2_relset_1(A_494, B_495, C_493, D_492) | ~m1_subset_1(D_492, k1_zfmisc_1(k2_zfmisc_1(A_494, B_495))) | ~m1_subset_1(C_493, k1_zfmisc_1(k2_zfmisc_1(A_494, B_495))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.42/2.02  tff(c_2874, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_56, c_2864])).
% 5.42/2.02  tff(c_2893, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2874])).
% 5.42/2.02  tff(c_2910, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2893])).
% 5.42/2.02  tff(c_3010, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_3004, c_2910])).
% 5.42/2.02  tff(c_3039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_3010])).
% 5.42/2.02  tff(c_3040, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2893])).
% 5.42/2.02  tff(c_3367, plain, (![A_614, B_615, C_616, D_617]: (k2_relset_1(A_614, B_615, C_616)=B_615 | ~r2_relset_1(B_615, B_615, k1_partfun1(B_615, A_614, A_614, B_615, D_617, C_616), k6_partfun1(B_615)) | ~m1_subset_1(D_617, k1_zfmisc_1(k2_zfmisc_1(B_615, A_614))) | ~v1_funct_2(D_617, B_615, A_614) | ~v1_funct_1(D_617) | ~m1_subset_1(C_616, k1_zfmisc_1(k2_zfmisc_1(A_614, B_615))) | ~v1_funct_2(C_616, A_614, B_615) | ~v1_funct_1(C_616))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.42/2.02  tff(c_3370, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3040, c_3367])).
% 5.42/2.02  tff(c_3375, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_68, c_66, c_64, c_2770, c_2832, c_3370])).
% 5.42/2.02  tff(c_38, plain, (![B_28]: (v2_funct_2(B_28, k2_relat_1(B_28)) | ~v5_relat_1(B_28, k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.42/2.02  tff(c_3381, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3375, c_38])).
% 5.42/2.02  tff(c_3385, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2650, c_2690, c_3375, c_3381])).
% 5.42/2.02  tff(c_3387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2588, c_3385])).
% 5.42/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.02  
% 5.42/2.02  Inference rules
% 5.42/2.02  ----------------------
% 5.42/2.02  #Ref     : 0
% 5.42/2.02  #Sup     : 749
% 5.42/2.02  #Fact    : 0
% 5.42/2.02  #Define  : 0
% 5.42/2.02  #Split   : 21
% 5.42/2.02  #Chain   : 0
% 5.42/2.02  #Close   : 0
% 5.42/2.02  
% 5.42/2.02  Ordering : KBO
% 5.42/2.02  
% 5.42/2.02  Simplification rules
% 5.42/2.02  ----------------------
% 5.42/2.02  #Subsume      : 80
% 5.42/2.02  #Demod        : 778
% 5.42/2.02  #Tautology    : 271
% 5.42/2.02  #SimpNegUnit  : 7
% 5.42/2.02  #BackRed      : 199
% 5.42/2.02  
% 5.42/2.02  #Partial instantiations: 0
% 5.42/2.02  #Strategies tried      : 1
% 5.42/2.02  
% 5.42/2.02  Timing (in seconds)
% 5.42/2.02  ----------------------
% 5.42/2.03  Preprocessing        : 0.34
% 5.42/2.03  Parsing              : 0.18
% 5.42/2.03  CNF conversion       : 0.02
% 5.42/2.03  Main loop            : 0.90
% 5.42/2.03  Inferencing          : 0.30
% 5.42/2.03  Reduction            : 0.32
% 5.42/2.03  Demodulation         : 0.23
% 5.42/2.03  BG Simplification    : 0.03
% 5.42/2.03  Subsumption          : 0.15
% 5.42/2.03  Abstraction          : 0.03
% 5.42/2.03  MUC search           : 0.00
% 5.42/2.03  Cooper               : 0.00
% 5.42/2.03  Total                : 1.30
% 5.42/2.03  Index Insertion      : 0.00
% 5.42/2.03  Index Deletion       : 0.00
% 5.42/2.03  Index Matching       : 0.00
% 5.42/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
