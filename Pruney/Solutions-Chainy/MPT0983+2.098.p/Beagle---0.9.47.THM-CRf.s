%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:15 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 6.01s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 554 expanded)
%              Number of leaves         :   45 ( 217 expanded)
%              Depth                    :   11
%              Number of atoms          :  268 (1772 expanded)
%              Number of equality atoms :   52 ( 201 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k4_mcart_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_82,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_104,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_66,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_120,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_30,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_44,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_14])).

tff(c_1208,plain,(
    ! [B_296,C_293,F_295,D_294,E_291,A_292] :
      ( m1_subset_1(k1_partfun1(A_292,B_296,C_293,D_294,E_291,F_295),k1_zfmisc_1(k2_zfmisc_1(A_292,D_294)))
      | ~ m1_subset_1(F_295,k1_zfmisc_1(k2_zfmisc_1(C_293,D_294)))
      | ~ v1_funct_1(F_295)
      | ~ m1_subset_1(E_291,k1_zfmisc_1(k2_zfmisc_1(A_292,B_296)))
      | ~ v1_funct_1(E_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    ! [A_20] : m1_subset_1(k6_relat_1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_67,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_28])).

tff(c_54,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1129,plain,(
    ! [D_274,C_275,A_276,B_277] :
      ( D_274 = C_275
      | ~ r2_relset_1(A_276,B_277,C_275,D_274)
      | ~ m1_subset_1(D_274,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277)))
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1141,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_1129])).

tff(c_1164,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1141])).

tff(c_1166,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1164])).

tff(c_1216,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1208,c_1166])).

tff(c_1244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_1216])).

tff(c_1245,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1164])).

tff(c_1805,plain,(
    ! [D_427,E_424,A_426,C_425,B_428] :
      ( k1_xboole_0 = C_425
      | v2_funct_1(D_427)
      | ~ v2_funct_1(k1_partfun1(A_426,B_428,B_428,C_425,D_427,E_424))
      | ~ m1_subset_1(E_424,k1_zfmisc_1(k2_zfmisc_1(B_428,C_425)))
      | ~ v1_funct_2(E_424,B_428,C_425)
      | ~ v1_funct_1(E_424)
      | ~ m1_subset_1(D_427,k1_zfmisc_1(k2_zfmisc_1(A_426,B_428)))
      | ~ v1_funct_2(D_427,A_426,B_428)
      | ~ v1_funct_1(D_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1807,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1245,c_1805])).

tff(c_1809,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_68,c_1807])).

tff(c_1810,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_1809])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1857,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1810,c_2])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1855,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1810,c_1810,c_6])).

tff(c_222,plain,(
    ! [C_81,B_82,A_83] :
      ( ~ v1_xboole_0(C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_235,plain,(
    ! [A_83] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_83,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_222])).

tff(c_264,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_1982,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1855,c_264])).

tff(c_1986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_1982])).

tff(c_1989,plain,(
    ! [A_439] : ~ r2_hidden(A_439,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_1994,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30,c_1989])).

tff(c_2019,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | A_21 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_30])).

tff(c_40,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,E_45] :
      ( m1_subset_1(k1_partfun1(A_41,B_42,C_43,D_44,E_45,F_46),k1_zfmisc_1(k2_zfmisc_1(A_41,D_44)))
      | ~ m1_subset_1(F_46,k1_zfmisc_1(k2_zfmisc_1(C_43,D_44)))
      | ~ v1_funct_1(F_46)
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(E_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2241,plain,(
    ! [D_471,C_472,A_473,B_474] :
      ( D_471 = C_472
      | ~ r2_relset_1(A_473,B_474,C_472,D_471)
      | ~ m1_subset_1(D_471,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474)))
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2251,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_2241])).

tff(c_2270,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2251])).

tff(c_2479,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2270])).

tff(c_2484,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2479])).

tff(c_2488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_2484])).

tff(c_2489,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2270])).

tff(c_50,plain,(
    ! [A_53,D_56,E_58,C_55,B_54] :
      ( k1_xboole_0 = C_55
      | v2_funct_1(D_56)
      | ~ v2_funct_1(k1_partfun1(A_53,B_54,B_54,C_55,D_56,E_58))
      | ~ m1_subset_1(E_58,k1_zfmisc_1(k2_zfmisc_1(B_54,C_55)))
      | ~ v1_funct_2(E_58,B_54,C_55)
      | ~ v1_funct_1(E_58)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(D_56,A_53,B_54)
      | ~ v1_funct_1(D_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2504,plain,(
    ! [C_524,B_527,D_526,A_525,E_523] :
      ( C_524 = '#skF_5'
      | v2_funct_1(D_526)
      | ~ v2_funct_1(k1_partfun1(A_525,B_527,B_527,C_524,D_526,E_523))
      | ~ m1_subset_1(E_523,k1_zfmisc_1(k2_zfmisc_1(B_527,C_524)))
      | ~ v1_funct_2(E_523,B_527,C_524)
      | ~ v1_funct_1(E_523)
      | ~ m1_subset_1(D_526,k1_zfmisc_1(k2_zfmisc_1(A_525,B_527)))
      | ~ v1_funct_2(D_526,A_525,B_527)
      | ~ v1_funct_1(D_526) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_50])).

tff(c_2506,plain,
    ( '#skF_5' = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2489,c_2504])).

tff(c_2508,plain,
    ( '#skF_5' = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_68,c_2506])).

tff(c_2509,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_2508])).

tff(c_2025,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_2])).

tff(c_2542,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2509,c_2025])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2022,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_1994,c_8])).

tff(c_2537,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2509,c_2509,c_2022])).

tff(c_236,plain,(
    ! [A_83] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_83,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_222])).

tff(c_2205,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_2714,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2205])).

tff(c_2718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_2714])).

tff(c_2726,plain,(
    ! [A_541] : ~ r2_hidden(A_541,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_2731,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2019,c_2726])).

tff(c_98,plain,(
    ! [A_63] : k6_relat_1(A_63) = k6_partfun1(A_63) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_104,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_12])).

tff(c_115,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_68])).

tff(c_2020,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_115])).

tff(c_2748,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2731,c_2020])).

tff(c_2758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_2748])).

tff(c_2759,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2777,plain,(
    ! [C_544,A_545,B_546] :
      ( v1_relat_1(C_544)
      | ~ m1_subset_1(C_544,k1_zfmisc_1(k2_zfmisc_1(A_545,B_546))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2793,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2777])).

tff(c_2835,plain,(
    ! [C_554,B_555,A_556] :
      ( v5_relat_1(C_554,B_555)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_556,B_555))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2853,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_2835])).

tff(c_2906,plain,(
    ! [A_570,B_571,D_572] :
      ( r2_relset_1(A_570,B_571,D_572,D_572)
      | ~ m1_subset_1(D_572,k1_zfmisc_1(k2_zfmisc_1(A_570,B_571))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2917,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_67,c_2906])).

tff(c_2988,plain,(
    ! [A_588,B_589,C_590] :
      ( k2_relset_1(A_588,B_589,C_590) = k2_relat_1(C_590)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(A_588,B_589))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3006,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2988])).

tff(c_3152,plain,(
    ! [E_627,D_630,F_631,A_628,C_629,B_632] :
      ( m1_subset_1(k1_partfun1(A_628,B_632,C_629,D_630,E_627,F_631),k1_zfmisc_1(k2_zfmisc_1(A_628,D_630)))
      | ~ m1_subset_1(F_631,k1_zfmisc_1(k2_zfmisc_1(C_629,D_630)))
      | ~ v1_funct_1(F_631)
      | ~ m1_subset_1(E_627,k1_zfmisc_1(k2_zfmisc_1(A_628,B_632)))
      | ~ v1_funct_1(E_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3053,plain,(
    ! [D_603,C_604,A_605,B_606] :
      ( D_603 = C_604
      | ~ r2_relset_1(A_605,B_606,C_604,D_603)
      | ~ m1_subset_1(D_603,k1_zfmisc_1(k2_zfmisc_1(A_605,B_606)))
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_605,B_606))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3065,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_3053])).

tff(c_3088,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_3065])).

tff(c_3109,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3088])).

tff(c_3160,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3152,c_3109])).

tff(c_3188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_3160])).

tff(c_3189,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3088])).

tff(c_3510,plain,(
    ! [A_721,B_722,C_723,D_724] :
      ( k2_relset_1(A_721,B_722,C_723) = B_722
      | ~ r2_relset_1(B_722,B_722,k1_partfun1(B_722,A_721,A_721,B_722,D_724,C_723),k6_partfun1(B_722))
      | ~ m1_subset_1(D_724,k1_zfmisc_1(k2_zfmisc_1(B_722,A_721)))
      | ~ v1_funct_2(D_724,B_722,A_721)
      | ~ v1_funct_1(D_724)
      | ~ m1_subset_1(C_723,k1_zfmisc_1(k2_zfmisc_1(A_721,B_722)))
      | ~ v1_funct_2(C_723,A_721,B_722)
      | ~ v1_funct_1(C_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3513,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3189,c_3510])).

tff(c_3518,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_2917,c_3006,c_3513])).

tff(c_36,plain,(
    ! [B_40] :
      ( v2_funct_2(B_40,k2_relat_1(B_40))
      | ~ v5_relat_1(B_40,k2_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3524,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3518,c_36])).

tff(c_3528,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2793,c_2853,c_3518,c_3524])).

tff(c_3530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2759,c_3528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.21  
% 5.60/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.21  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k4_mcart_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.60/2.21  
% 5.60/2.21  %Foreground sorts:
% 5.60/2.21  
% 5.60/2.21  
% 5.60/2.21  %Background operators:
% 5.60/2.21  
% 5.60/2.21  
% 5.60/2.21  %Foreground operators:
% 5.60/2.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.60/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.60/2.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.60/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.60/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.60/2.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.60/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.60/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.60/2.21  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.60/2.21  tff('#skF_5', type, '#skF_5': $i).
% 5.60/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.60/2.21  tff('#skF_2', type, '#skF_2': $i).
% 5.60/2.21  tff('#skF_3', type, '#skF_3': $i).
% 5.60/2.21  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.60/2.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.60/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.60/2.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.60/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.60/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.60/2.21  tff('#skF_4', type, '#skF_4': $i).
% 5.60/2.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.60/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.60/2.21  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.60/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.60/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.60/2.21  
% 6.01/2.23  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.01/2.23  tff(f_82, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 6.01/2.23  tff(f_104, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.01/2.23  tff(f_42, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 6.01/2.23  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.01/2.23  tff(f_66, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.01/2.23  tff(f_64, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.01/2.23  tff(f_143, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.01/2.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.01/2.23  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.01/2.23  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.01/2.23  tff(f_40, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.01/2.23  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.01/2.23  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.01/2.23  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.01/2.23  tff(f_121, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.01/2.23  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.01/2.23  tff(c_52, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.01/2.23  tff(c_120, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 6.01/2.23  tff(c_30, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.01/2.23  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.01/2.23  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.01/2.23  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.01/2.23  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.01/2.23  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.01/2.23  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.01/2.23  tff(c_44, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.01/2.23  tff(c_14, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.01/2.23  tff(c_68, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_14])).
% 6.01/2.23  tff(c_1208, plain, (![B_296, C_293, F_295, D_294, E_291, A_292]: (m1_subset_1(k1_partfun1(A_292, B_296, C_293, D_294, E_291, F_295), k1_zfmisc_1(k2_zfmisc_1(A_292, D_294))) | ~m1_subset_1(F_295, k1_zfmisc_1(k2_zfmisc_1(C_293, D_294))) | ~v1_funct_1(F_295) | ~m1_subset_1(E_291, k1_zfmisc_1(k2_zfmisc_1(A_292, B_296))) | ~v1_funct_1(E_291))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.01/2.23  tff(c_28, plain, (![A_20]: (m1_subset_1(k6_relat_1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.01/2.23  tff(c_67, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_28])).
% 6.01/2.23  tff(c_54, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.01/2.23  tff(c_1129, plain, (![D_274, C_275, A_276, B_277]: (D_274=C_275 | ~r2_relset_1(A_276, B_277, C_275, D_274) | ~m1_subset_1(D_274, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.01/2.23  tff(c_1141, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_1129])).
% 6.01/2.23  tff(c_1164, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1141])).
% 6.01/2.23  tff(c_1166, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1164])).
% 6.01/2.23  tff(c_1216, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1208, c_1166])).
% 6.01/2.23  tff(c_1244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_1216])).
% 6.01/2.23  tff(c_1245, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1164])).
% 6.01/2.23  tff(c_1805, plain, (![D_427, E_424, A_426, C_425, B_428]: (k1_xboole_0=C_425 | v2_funct_1(D_427) | ~v2_funct_1(k1_partfun1(A_426, B_428, B_428, C_425, D_427, E_424)) | ~m1_subset_1(E_424, k1_zfmisc_1(k2_zfmisc_1(B_428, C_425))) | ~v1_funct_2(E_424, B_428, C_425) | ~v1_funct_1(E_424) | ~m1_subset_1(D_427, k1_zfmisc_1(k2_zfmisc_1(A_426, B_428))) | ~v1_funct_2(D_427, A_426, B_428) | ~v1_funct_1(D_427))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.01/2.23  tff(c_1807, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1245, c_1805])).
% 6.01/2.23  tff(c_1809, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_68, c_1807])).
% 6.01/2.23  tff(c_1810, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_120, c_1809])).
% 6.01/2.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.01/2.23  tff(c_1857, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1810, c_2])).
% 6.01/2.23  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.01/2.23  tff(c_1855, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1810, c_1810, c_6])).
% 6.01/2.23  tff(c_222, plain, (![C_81, B_82, A_83]: (~v1_xboole_0(C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.01/2.23  tff(c_235, plain, (![A_83]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_83, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_222])).
% 6.01/2.23  tff(c_264, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_235])).
% 6.01/2.23  tff(c_1982, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1855, c_264])).
% 6.01/2.23  tff(c_1986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1857, c_1982])).
% 6.01/2.23  tff(c_1989, plain, (![A_439]: (~r2_hidden(A_439, '#skF_5'))), inference(splitRight, [status(thm)], [c_235])).
% 6.01/2.23  tff(c_1994, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_30, c_1989])).
% 6.01/2.23  tff(c_2019, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | A_21='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_30])).
% 6.01/2.23  tff(c_40, plain, (![D_44, F_46, C_43, A_41, B_42, E_45]: (m1_subset_1(k1_partfun1(A_41, B_42, C_43, D_44, E_45, F_46), k1_zfmisc_1(k2_zfmisc_1(A_41, D_44))) | ~m1_subset_1(F_46, k1_zfmisc_1(k2_zfmisc_1(C_43, D_44))) | ~v1_funct_1(F_46) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(E_45))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.01/2.23  tff(c_2241, plain, (![D_471, C_472, A_473, B_474]: (D_471=C_472 | ~r2_relset_1(A_473, B_474, C_472, D_471) | ~m1_subset_1(D_471, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.01/2.23  tff(c_2251, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_2241])).
% 6.01/2.23  tff(c_2270, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2251])).
% 6.01/2.23  tff(c_2479, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2270])).
% 6.01/2.23  tff(c_2484, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_2479])).
% 6.01/2.23  tff(c_2488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_2484])).
% 6.01/2.23  tff(c_2489, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2270])).
% 6.01/2.23  tff(c_50, plain, (![A_53, D_56, E_58, C_55, B_54]: (k1_xboole_0=C_55 | v2_funct_1(D_56) | ~v2_funct_1(k1_partfun1(A_53, B_54, B_54, C_55, D_56, E_58)) | ~m1_subset_1(E_58, k1_zfmisc_1(k2_zfmisc_1(B_54, C_55))) | ~v1_funct_2(E_58, B_54, C_55) | ~v1_funct_1(E_58) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(D_56, A_53, B_54) | ~v1_funct_1(D_56))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.01/2.23  tff(c_2504, plain, (![C_524, B_527, D_526, A_525, E_523]: (C_524='#skF_5' | v2_funct_1(D_526) | ~v2_funct_1(k1_partfun1(A_525, B_527, B_527, C_524, D_526, E_523)) | ~m1_subset_1(E_523, k1_zfmisc_1(k2_zfmisc_1(B_527, C_524))) | ~v1_funct_2(E_523, B_527, C_524) | ~v1_funct_1(E_523) | ~m1_subset_1(D_526, k1_zfmisc_1(k2_zfmisc_1(A_525, B_527))) | ~v1_funct_2(D_526, A_525, B_527) | ~v1_funct_1(D_526))), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_50])).
% 6.01/2.23  tff(c_2506, plain, ('#skF_5'='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2489, c_2504])).
% 6.01/2.23  tff(c_2508, plain, ('#skF_5'='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_68, c_2506])).
% 6.01/2.23  tff(c_2509, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_120, c_2508])).
% 6.01/2.23  tff(c_2025, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_2])).
% 6.01/2.23  tff(c_2542, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2509, c_2025])).
% 6.01/2.23  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.01/2.23  tff(c_2022, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_1994, c_8])).
% 6.01/2.23  tff(c_2537, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2509, c_2509, c_2022])).
% 6.01/2.23  tff(c_236, plain, (![A_83]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_83, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_222])).
% 6.01/2.23  tff(c_2205, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_236])).
% 6.01/2.23  tff(c_2714, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2205])).
% 6.01/2.23  tff(c_2718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2542, c_2714])).
% 6.01/2.23  tff(c_2726, plain, (![A_541]: (~r2_hidden(A_541, '#skF_4'))), inference(splitRight, [status(thm)], [c_236])).
% 6.01/2.23  tff(c_2731, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_2019, c_2726])).
% 6.01/2.23  tff(c_98, plain, (![A_63]: (k6_relat_1(A_63)=k6_partfun1(A_63))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.01/2.23  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.01/2.23  tff(c_104, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_98, c_12])).
% 6.01/2.23  tff(c_115, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104, c_68])).
% 6.01/2.23  tff(c_2020, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_115])).
% 6.01/2.23  tff(c_2748, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2731, c_2020])).
% 6.01/2.23  tff(c_2758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_2748])).
% 6.01/2.23  tff(c_2759, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 6.01/2.23  tff(c_2777, plain, (![C_544, A_545, B_546]: (v1_relat_1(C_544) | ~m1_subset_1(C_544, k1_zfmisc_1(k2_zfmisc_1(A_545, B_546))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.01/2.23  tff(c_2793, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2777])).
% 6.01/2.23  tff(c_2835, plain, (![C_554, B_555, A_556]: (v5_relat_1(C_554, B_555) | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_556, B_555))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.01/2.23  tff(c_2853, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_2835])).
% 6.01/2.23  tff(c_2906, plain, (![A_570, B_571, D_572]: (r2_relset_1(A_570, B_571, D_572, D_572) | ~m1_subset_1(D_572, k1_zfmisc_1(k2_zfmisc_1(A_570, B_571))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.01/2.23  tff(c_2917, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_67, c_2906])).
% 6.01/2.23  tff(c_2988, plain, (![A_588, B_589, C_590]: (k2_relset_1(A_588, B_589, C_590)=k2_relat_1(C_590) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(A_588, B_589))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.01/2.23  tff(c_3006, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2988])).
% 6.01/2.23  tff(c_3152, plain, (![E_627, D_630, F_631, A_628, C_629, B_632]: (m1_subset_1(k1_partfun1(A_628, B_632, C_629, D_630, E_627, F_631), k1_zfmisc_1(k2_zfmisc_1(A_628, D_630))) | ~m1_subset_1(F_631, k1_zfmisc_1(k2_zfmisc_1(C_629, D_630))) | ~v1_funct_1(F_631) | ~m1_subset_1(E_627, k1_zfmisc_1(k2_zfmisc_1(A_628, B_632))) | ~v1_funct_1(E_627))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.01/2.23  tff(c_3053, plain, (![D_603, C_604, A_605, B_606]: (D_603=C_604 | ~r2_relset_1(A_605, B_606, C_604, D_603) | ~m1_subset_1(D_603, k1_zfmisc_1(k2_zfmisc_1(A_605, B_606))) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_605, B_606))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.01/2.23  tff(c_3065, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_3053])).
% 6.01/2.23  tff(c_3088, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_3065])).
% 6.01/2.23  tff(c_3109, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_3088])).
% 6.01/2.23  tff(c_3160, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_3152, c_3109])).
% 6.01/2.23  tff(c_3188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_3160])).
% 6.01/2.23  tff(c_3189, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3088])).
% 6.01/2.23  tff(c_3510, plain, (![A_721, B_722, C_723, D_724]: (k2_relset_1(A_721, B_722, C_723)=B_722 | ~r2_relset_1(B_722, B_722, k1_partfun1(B_722, A_721, A_721, B_722, D_724, C_723), k6_partfun1(B_722)) | ~m1_subset_1(D_724, k1_zfmisc_1(k2_zfmisc_1(B_722, A_721))) | ~v1_funct_2(D_724, B_722, A_721) | ~v1_funct_1(D_724) | ~m1_subset_1(C_723, k1_zfmisc_1(k2_zfmisc_1(A_721, B_722))) | ~v1_funct_2(C_723, A_721, B_722) | ~v1_funct_1(C_723))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.01/2.23  tff(c_3513, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3189, c_3510])).
% 6.01/2.23  tff(c_3518, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_2917, c_3006, c_3513])).
% 6.01/2.23  tff(c_36, plain, (![B_40]: (v2_funct_2(B_40, k2_relat_1(B_40)) | ~v5_relat_1(B_40, k2_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.01/2.23  tff(c_3524, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3518, c_36])).
% 6.01/2.23  tff(c_3528, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2793, c_2853, c_3518, c_3524])).
% 6.01/2.23  tff(c_3530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2759, c_3528])).
% 6.01/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.01/2.23  
% 6.01/2.23  Inference rules
% 6.01/2.23  ----------------------
% 6.01/2.23  #Ref     : 0
% 6.01/2.23  #Sup     : 751
% 6.01/2.23  #Fact    : 0
% 6.01/2.23  #Define  : 0
% 6.01/2.23  #Split   : 18
% 6.01/2.23  #Chain   : 0
% 6.01/2.23  #Close   : 0
% 6.01/2.23  
% 6.01/2.23  Ordering : KBO
% 6.01/2.23  
% 6.01/2.23  Simplification rules
% 6.01/2.23  ----------------------
% 6.01/2.23  #Subsume      : 74
% 6.01/2.23  #Demod        : 965
% 6.01/2.23  #Tautology    : 236
% 6.01/2.23  #SimpNegUnit  : 10
% 6.01/2.23  #BackRed      : 273
% 6.01/2.23  
% 6.01/2.23  #Partial instantiations: 0
% 6.01/2.23  #Strategies tried      : 1
% 6.01/2.23  
% 6.01/2.23  Timing (in seconds)
% 6.01/2.23  ----------------------
% 6.01/2.23  Preprocessing        : 0.40
% 6.01/2.23  Parsing              : 0.22
% 6.01/2.23  CNF conversion       : 0.02
% 6.01/2.23  Main loop            : 0.98
% 6.01/2.23  Inferencing          : 0.33
% 6.01/2.23  Reduction            : 0.36
% 6.01/2.23  Demodulation         : 0.26
% 6.01/2.23  BG Simplification    : 0.04
% 6.01/2.23  Subsumption          : 0.16
% 6.01/2.23  Abstraction          : 0.04
% 6.01/2.23  MUC search           : 0.00
% 6.01/2.24  Cooper               : 0.00
% 6.01/2.24  Total                : 1.42
% 6.01/2.24  Index Insertion      : 0.00
% 6.01/2.24  Index Deletion       : 0.00
% 6.01/2.24  Index Matching       : 0.00
% 6.01/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
