%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:38 EST 2020

% Result     : Theorem 9.41s
% Output     : CNFRefutation 9.41s
% Verified   : 
% Statistics : Number of formulae       :  179 (1503 expanded)
%              Number of leaves         :   36 ( 507 expanded)
%              Depth                    :   18
%              Number of atoms          :  370 (4593 expanded)
%              Number of equality atoms :  133 ( 984 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_140,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ! [D] :
          ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( r2_relset_1(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r2_hidden(k4_tarski(E,F),C)
                    <=> r2_hidden(k4_tarski(E,F),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).

tff(f_119,axiom,(
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

tff(f_71,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_153,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_164,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_153])).

tff(c_76,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_74,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4933,plain,(
    ! [A_840,B_841,C_842] :
      ( k1_relset_1(A_840,B_841,C_842) = k1_relat_1(C_842)
      | ~ m1_subset_1(C_842,k1_zfmisc_1(k2_zfmisc_1(A_840,B_841))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4946,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_4933])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5360,plain,(
    ! [A_907,B_908,C_909,D_910] :
      ( m1_subset_1('#skF_3'(A_907,B_908,C_909,D_910),A_907)
      | r2_relset_1(A_907,B_908,C_909,D_910)
      | ~ m1_subset_1(D_910,k1_zfmisc_1(k2_zfmisc_1(A_907,B_908)))
      | ~ m1_subset_1(C_909,k1_zfmisc_1(k2_zfmisc_1(A_907,B_908))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5438,plain,(
    ! [C_915] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_6',C_915,'#skF_8'),'#skF_5')
      | r2_relset_1('#skF_5','#skF_6',C_915,'#skF_8')
      | ~ m1_subset_1(C_915,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_66,c_5360])).

tff(c_5448,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_8','#skF_8'),'#skF_5')
    | r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_5438])).

tff(c_5449,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5448])).

tff(c_5091,plain,(
    ! [B_871,A_872,C_873] :
      ( k1_xboole_0 = B_871
      | k1_relset_1(A_872,B_871,C_873) = A_872
      | ~ v1_funct_2(C_873,A_872,B_871)
      | ~ m1_subset_1(C_873,k1_zfmisc_1(k2_zfmisc_1(A_872,B_871))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5094,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_5091])).

tff(c_5106,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4946,c_5094])).

tff(c_5111,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5106])).

tff(c_165,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_153])).

tff(c_70,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_68,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4947,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_4933])).

tff(c_5097,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_5091])).

tff(c_5109,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4947,c_5097])).

tff(c_5117,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5109])).

tff(c_5242,plain,(
    ! [A_891,B_892] :
      ( r2_hidden('#skF_2'(A_891,B_892),k1_relat_1(A_891))
      | B_892 = A_891
      | k1_relat_1(B_892) != k1_relat_1(A_891)
      | ~ v1_funct_1(B_892)
      | ~ v1_relat_1(B_892)
      | ~ v1_funct_1(A_891)
      | ~ v1_relat_1(A_891) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5252,plain,(
    ! [B_892] :
      ( r2_hidden('#skF_2'('#skF_8',B_892),'#skF_5')
      | B_892 = '#skF_8'
      | k1_relat_1(B_892) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_892)
      | ~ v1_relat_1(B_892)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5117,c_5242])).

tff(c_5264,plain,(
    ! [B_895] :
      ( r2_hidden('#skF_2'('#skF_8',B_895),'#skF_5')
      | B_895 = '#skF_8'
      | k1_relat_1(B_895) != '#skF_5'
      | ~ v1_funct_1(B_895)
      | ~ v1_relat_1(B_895) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_70,c_5117,c_5252])).

tff(c_64,plain,(
    ! [E_63] :
      ( k1_funct_1('#skF_7',E_63) = k1_funct_1('#skF_8',E_63)
      | ~ r2_hidden(E_63,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5818,plain,(
    ! [B_988] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_8',B_988)) = k1_funct_1('#skF_8','#skF_2'('#skF_8',B_988))
      | B_988 = '#skF_8'
      | k1_relat_1(B_988) != '#skF_5'
      | ~ v1_funct_1(B_988)
      | ~ v1_relat_1(B_988) ) ),
    inference(resolution,[status(thm)],[c_5264,c_64])).

tff(c_24,plain,(
    ! [B_19,A_15] :
      ( k1_funct_1(B_19,'#skF_2'(A_15,B_19)) != k1_funct_1(A_15,'#skF_2'(A_15,B_19))
      | B_19 = A_15
      | k1_relat_1(B_19) != k1_relat_1(A_15)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5825,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5818,c_24])).

tff(c_5832,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_5111,c_165,c_70,c_5117,c_5111,c_5825])).

tff(c_62,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5868,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5832,c_62])).

tff(c_5880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5449,c_5868])).

tff(c_5882,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(splitRight,[status(thm)],[c_5448])).

tff(c_42,plain,(
    ! [A_26,B_27,C_28,D_42] :
      ( r2_hidden(k4_tarski('#skF_3'(A_26,B_27,C_28,D_42),'#skF_4'(A_26,B_27,C_28,D_42)),C_28)
      | r2_hidden(k4_tarski('#skF_3'(A_26,B_27,C_28,D_42),'#skF_4'(A_26,B_27,C_28,D_42)),D_42)
      | r2_relset_1(A_26,B_27,C_28,D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7317,plain,(
    ! [A_26,B_27,D_42] :
      ( r2_relset_1(A_26,B_27,D_42,D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | r2_hidden(k4_tarski('#skF_3'(A_26,B_27,D_42,D_42),'#skF_4'(A_26,B_27,D_42,D_42)),D_42) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_42])).

tff(c_8035,plain,(
    ! [A_1315,B_1316,D_1317] :
      ( r2_relset_1(A_1315,B_1316,D_1317,D_1317)
      | ~ m1_subset_1(D_1317,k1_zfmisc_1(k2_zfmisc_1(A_1315,B_1316)))
      | r2_hidden(k4_tarski('#skF_3'(A_1315,B_1316,D_1317,D_1317),'#skF_4'(A_1315,B_1316,D_1317,D_1317)),D_1317) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_42])).

tff(c_36,plain,(
    ! [A_26,B_27,C_28,D_42] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_26,B_27,C_28,D_42),'#skF_4'(A_26,B_27,C_28,D_42)),D_42)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_26,B_27,C_28,D_42),'#skF_4'(A_26,B_27,C_28,D_42)),C_28)
      | r2_relset_1(A_26,B_27,C_28,D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8115,plain,(
    ! [A_1332,B_1333,D_1334] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_1332,B_1333,D_1334,D_1334),'#skF_4'(A_1332,B_1333,D_1334,D_1334)),D_1334)
      | r2_relset_1(A_1332,B_1333,D_1334,D_1334)
      | ~ m1_subset_1(D_1334,k1_zfmisc_1(k2_zfmisc_1(A_1332,B_1333))) ) ),
    inference(resolution,[status(thm)],[c_8035,c_36])).

tff(c_8124,plain,(
    ! [A_1335,B_1336,D_1337] :
      ( r2_relset_1(A_1335,B_1336,D_1337,D_1337)
      | ~ m1_subset_1(D_1337,k1_zfmisc_1(k2_zfmisc_1(A_1335,B_1336))) ) ),
    inference(resolution,[status(thm)],[c_7317,c_8115])).

tff(c_8132,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_8124])).

tff(c_8142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5882,c_8132])).

tff(c_8143,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5109])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8168,plain,(
    ! [A_8] : r1_tarski('#skF_6',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8143,c_14])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8166,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8143,c_8143,c_18])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_184,plain,(
    ! [C_89,A_90,B_91] :
      ( r2_hidden(C_89,A_90)
      | ~ r2_hidden(C_89,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5015,plain,(
    ! [A_853,B_854,A_855] :
      ( r2_hidden('#skF_1'(A_853,B_854),A_855)
      | ~ m1_subset_1(A_853,k1_zfmisc_1(A_855))
      | r1_tarski(A_853,B_854) ) ),
    inference(resolution,[status(thm)],[c_6,c_184])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5036,plain,(
    ! [A_856,A_857] :
      ( ~ m1_subset_1(A_856,k1_zfmisc_1(A_857))
      | r1_tarski(A_856,A_857) ) ),
    inference(resolution,[status(thm)],[c_5015,c_4])).

tff(c_5049,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_5036])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5060,plain,
    ( k2_zfmisc_1('#skF_5','#skF_6') = '#skF_8'
    | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_5049,c_8])).

tff(c_5064,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5060])).

tff(c_8207,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8166,c_5064])).

tff(c_8215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8168,c_8207])).

tff(c_8216,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5106])).

tff(c_8237,plain,(
    ! [A_8] : r1_tarski('#skF_6',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8216,c_14])).

tff(c_8235,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8216,c_8216,c_18])).

tff(c_8296,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8235,c_5064])).

tff(c_8304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8237,c_8296])).

tff(c_8305,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5060])).

tff(c_8310,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8305,c_72])).

tff(c_8425,plain,(
    ! [B_1367,A_1368,C_1369] :
      ( k1_xboole_0 = B_1367
      | k1_relset_1(A_1368,B_1367,C_1369) = A_1368
      | ~ v1_funct_2(C_1369,A_1368,B_1367)
      | ~ m1_subset_1(C_1369,k1_zfmisc_1(k2_zfmisc_1(A_1368,B_1367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8428,plain,(
    ! [C_1369] :
      ( k1_xboole_0 = '#skF_6'
      | k1_relset_1('#skF_5','#skF_6',C_1369) = '#skF_5'
      | ~ v1_funct_2(C_1369,'#skF_5','#skF_6')
      | ~ m1_subset_1(C_1369,k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8305,c_8425])).

tff(c_8538,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8428])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8321,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_8305,c_16])).

tff(c_8359,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_8321])).

tff(c_8543,plain,(
    '#skF_6' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8538,c_8359])).

tff(c_8623,plain,(
    ! [A_1402] : k2_zfmisc_1(A_1402,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8538,c_8538,c_18])).

tff(c_8632,plain,(
    '#skF_6' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_8623,c_8305])).

tff(c_8649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8543,c_8632])).

tff(c_8652,plain,(
    ! [C_1403] :
      ( k1_relset_1('#skF_5','#skF_6',C_1403) = '#skF_5'
      | ~ v1_funct_2(C_1403,'#skF_5','#skF_6')
      | ~ m1_subset_1(C_1403,k1_zfmisc_1('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_8428])).

tff(c_8658,plain,
    ( k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_8310,c_8652])).

tff(c_8664,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4946,c_8658])).

tff(c_8311,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8305,c_66])).

tff(c_8655,plain,
    ( k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_8311,c_8652])).

tff(c_8661,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4947,c_8655])).

tff(c_26,plain,(
    ! [A_15,B_19] :
      ( r2_hidden('#skF_2'(A_15,B_19),k1_relat_1(A_15))
      | B_19 = A_15
      | k1_relat_1(B_19) != k1_relat_1(A_15)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8669,plain,(
    ! [B_19] :
      ( r2_hidden('#skF_2'('#skF_8',B_19),'#skF_5')
      | B_19 = '#skF_8'
      | k1_relat_1(B_19) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8661,c_26])).

tff(c_8717,plain,(
    ! [B_1409] :
      ( r2_hidden('#skF_2'('#skF_8',B_1409),'#skF_5')
      | B_1409 = '#skF_8'
      | k1_relat_1(B_1409) != '#skF_5'
      | ~ v1_funct_1(B_1409)
      | ~ v1_relat_1(B_1409) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_70,c_8661,c_8669])).

tff(c_8889,plain,(
    ! [B_1447] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_8',B_1447)) = k1_funct_1('#skF_8','#skF_2'('#skF_8',B_1447))
      | B_1447 = '#skF_8'
      | k1_relat_1(B_1447) != '#skF_5'
      | ~ v1_funct_1(B_1447)
      | ~ v1_relat_1(B_1447) ) ),
    inference(resolution,[status(thm)],[c_8717,c_64])).

tff(c_8896,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_8889,c_24])).

tff(c_8903,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_8664,c_165,c_70,c_8664,c_8661,c_8896])).

tff(c_5048,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_72,c_5036])).

tff(c_5057,plain,
    ( k2_zfmisc_1('#skF_5','#skF_6') = '#skF_7'
    | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_5048,c_8])).

tff(c_5063,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_5057])).

tff(c_8307,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8305,c_5063])).

tff(c_8929,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8903,c_8307])).

tff(c_8944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8929])).

tff(c_8946,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_8321])).

tff(c_8964,plain,(
    ! [A_8] : r1_tarski('#skF_8',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8946,c_14])).

tff(c_8973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8964,c_8307])).

tff(c_8974,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_5057])).

tff(c_8978,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8974,c_72])).

tff(c_9030,plain,(
    ! [B_1451,C_1452,A_1453] :
      ( k1_xboole_0 = B_1451
      | v1_funct_2(C_1452,A_1453,B_1451)
      | k1_relset_1(A_1453,B_1451,C_1452) != A_1453
      | ~ m1_subset_1(C_1452,k1_zfmisc_1(k2_zfmisc_1(A_1453,B_1451))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9033,plain,(
    ! [C_1452] :
      ( k1_xboole_0 = '#skF_6'
      | v1_funct_2(C_1452,'#skF_5','#skF_6')
      | k1_relset_1('#skF_5','#skF_6',C_1452) != '#skF_5'
      | ~ m1_subset_1(C_1452,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8974,c_9030])).

tff(c_9068,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9033])).

tff(c_8989,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_8974,c_16])).

tff(c_9029,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_8989])).

tff(c_9071,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9068,c_9029])).

tff(c_9087,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9068,c_9068,c_18])).

tff(c_9120,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9087,c_8974])).

tff(c_9122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9071,c_9120])).

tff(c_9124,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9033])).

tff(c_9180,plain,(
    ! [B_1477,A_1478,C_1479] :
      ( k1_xboole_0 = B_1477
      | k1_relset_1(A_1478,B_1477,C_1479) = A_1478
      | ~ v1_funct_2(C_1479,A_1478,B_1477)
      | ~ m1_subset_1(C_1479,k1_zfmisc_1(k2_zfmisc_1(A_1478,B_1477))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9183,plain,(
    ! [C_1479] :
      ( k1_xboole_0 = '#skF_6'
      | k1_relset_1('#skF_5','#skF_6',C_1479) = '#skF_5'
      | ~ v1_funct_2(C_1479,'#skF_5','#skF_6')
      | ~ m1_subset_1(C_1479,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8974,c_9180])).

tff(c_9192,plain,(
    ! [C_1480] :
      ( k1_relset_1('#skF_5','#skF_6',C_1480) = '#skF_5'
      | ~ v1_funct_2(C_1480,'#skF_5','#skF_6')
      | ~ m1_subset_1(C_1480,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9124,c_9183])).

tff(c_9198,plain,
    ( k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_8978,c_9192])).

tff(c_9204,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4946,c_9198])).

tff(c_8979,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8974,c_66])).

tff(c_9195,plain,
    ( k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_8979,c_9192])).

tff(c_9201,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4947,c_9195])).

tff(c_9278,plain,(
    ! [A_1492,B_1493] :
      ( r2_hidden('#skF_2'(A_1492,B_1493),k1_relat_1(A_1492))
      | B_1493 = A_1492
      | k1_relat_1(B_1493) != k1_relat_1(A_1492)
      | ~ v1_funct_1(B_1493)
      | ~ v1_relat_1(B_1493)
      | ~ v1_funct_1(A_1492)
      | ~ v1_relat_1(A_1492) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9291,plain,(
    ! [B_1493] :
      ( r2_hidden('#skF_2'('#skF_8',B_1493),'#skF_5')
      | B_1493 = '#skF_8'
      | k1_relat_1(B_1493) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_1493)
      | ~ v1_relat_1(B_1493)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9201,c_9278])).

tff(c_9316,plain,(
    ! [B_1495] :
      ( r2_hidden('#skF_2'('#skF_8',B_1495),'#skF_5')
      | B_1495 = '#skF_8'
      | k1_relat_1(B_1495) != '#skF_5'
      | ~ v1_funct_1(B_1495)
      | ~ v1_relat_1(B_1495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_70,c_9201,c_9291])).

tff(c_9329,plain,(
    ! [B_1495] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_8',B_1495)) = k1_funct_1('#skF_8','#skF_2'('#skF_8',B_1495))
      | B_1495 = '#skF_8'
      | k1_relat_1(B_1495) != '#skF_5'
      | ~ v1_funct_1(B_1495)
      | ~ v1_relat_1(B_1495) ) ),
    inference(resolution,[status(thm)],[c_9316,c_64])).

tff(c_9539,plain,(
    ! [B_1549,A_1550] :
      ( k1_funct_1(B_1549,'#skF_2'(A_1550,B_1549)) != k1_funct_1(A_1550,'#skF_2'(A_1550,B_1549))
      | B_1549 = A_1550
      | k1_relat_1(B_1549) != k1_relat_1(A_1550)
      | ~ v1_funct_1(B_1549)
      | ~ v1_relat_1(B_1549)
      | ~ v1_funct_1(A_1550)
      | ~ v1_relat_1(A_1550) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9543,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_9329,c_9539])).

tff(c_9549,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_9204,c_165,c_70,c_9204,c_9201,c_9543])).

tff(c_9016,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8974,c_8974,c_5060])).

tff(c_9017,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_9016])).

tff(c_9586,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9549,c_9017])).

tff(c_9603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9586])).

tff(c_9605,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_8989])).

tff(c_9623,plain,(
    ! [A_8] : r1_tarski('#skF_7',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9605,c_14])).

tff(c_9632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9623,c_9017])).

tff(c_9633,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_9016])).

tff(c_9673,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9633,c_62])).

tff(c_9663,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9633,c_8979])).

tff(c_9666,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9633,c_8974])).

tff(c_10475,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_relset_1(A_26,B_27,C_28,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | r2_hidden(k4_tarski('#skF_3'(A_26,B_27,C_28,C_28),'#skF_4'(A_26,B_27,C_28,C_28)),C_28) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_42])).

tff(c_10566,plain,(
    ! [A_1706,B_1707,C_1708,D_1709] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_1706,B_1707,C_1708,D_1709),'#skF_4'(A_1706,B_1707,C_1708,D_1709)),D_1709)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1706,B_1707,C_1708,D_1709),'#skF_4'(A_1706,B_1707,C_1708,D_1709)),C_1708)
      | r2_relset_1(A_1706,B_1707,C_1708,D_1709)
      | ~ m1_subset_1(D_1709,k1_zfmisc_1(k2_zfmisc_1(A_1706,B_1707)))
      | ~ m1_subset_1(C_1708,k1_zfmisc_1(k2_zfmisc_1(A_1706,B_1707))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10574,plain,(
    ! [A_1710,B_1711,C_1712] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_1710,B_1711,C_1712,C_1712),'#skF_4'(A_1710,B_1711,C_1712,C_1712)),C_1712)
      | r2_relset_1(A_1710,B_1711,C_1712,C_1712)
      | ~ m1_subset_1(C_1712,k1_zfmisc_1(k2_zfmisc_1(A_1710,B_1711))) ) ),
    inference(resolution,[status(thm)],[c_10475,c_10566])).

tff(c_10583,plain,(
    ! [A_1713,B_1714,C_1715] :
      ( r2_relset_1(A_1713,B_1714,C_1715,C_1715)
      | ~ m1_subset_1(C_1715,k1_zfmisc_1(k2_zfmisc_1(A_1713,B_1714))) ) ),
    inference(resolution,[status(thm)],[c_10475,c_10574])).

tff(c_10598,plain,(
    ! [C_1716] :
      ( r2_relset_1('#skF_5','#skF_6',C_1716,C_1716)
      | ~ m1_subset_1(C_1716,k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9666,c_10583])).

tff(c_10606,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_9663,c_10598])).

tff(c_10612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9673,c_10606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.41/3.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.26  
% 9.41/3.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.26  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3 > #skF_1
% 9.41/3.26  
% 9.41/3.26  %Foreground sorts:
% 9.41/3.26  
% 9.41/3.26  
% 9.41/3.26  %Background operators:
% 9.41/3.26  
% 9.41/3.26  
% 9.41/3.26  %Foreground operators:
% 9.41/3.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.41/3.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.41/3.26  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.41/3.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.41/3.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.41/3.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.41/3.26  tff('#skF_7', type, '#skF_7': $i).
% 9.41/3.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.41/3.26  tff('#skF_5', type, '#skF_5': $i).
% 9.41/3.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.41/3.26  tff('#skF_6', type, '#skF_6': $i).
% 9.41/3.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.41/3.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.41/3.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.41/3.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 9.41/3.26  tff('#skF_8', type, '#skF_8': $i).
% 9.41/3.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.41/3.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.41/3.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.41/3.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.41/3.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.41/3.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.41/3.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.41/3.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.41/3.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.41/3.26  
% 9.41/3.29  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.41/3.29  tff(f_140, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 9.41/3.29  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.41/3.29  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.41/3.29  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (r2_hidden(k4_tarski(E, F), C) <=> r2_hidden(k4_tarski(E, F), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relset_1)).
% 9.41/3.29  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.41/3.29  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 9.41/3.29  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.41/3.29  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.41/3.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.41/3.29  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 9.41/3.29  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.41/3.29  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.41/3.29  tff(c_153, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.41/3.29  tff(c_164, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_153])).
% 9.41/3.29  tff(c_76, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.41/3.29  tff(c_74, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.41/3.29  tff(c_4933, plain, (![A_840, B_841, C_842]: (k1_relset_1(A_840, B_841, C_842)=k1_relat_1(C_842) | ~m1_subset_1(C_842, k1_zfmisc_1(k2_zfmisc_1(A_840, B_841))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.41/3.29  tff(c_4946, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_4933])).
% 9.41/3.29  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.41/3.29  tff(c_5360, plain, (![A_907, B_908, C_909, D_910]: (m1_subset_1('#skF_3'(A_907, B_908, C_909, D_910), A_907) | r2_relset_1(A_907, B_908, C_909, D_910) | ~m1_subset_1(D_910, k1_zfmisc_1(k2_zfmisc_1(A_907, B_908))) | ~m1_subset_1(C_909, k1_zfmisc_1(k2_zfmisc_1(A_907, B_908))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.41/3.29  tff(c_5438, plain, (![C_915]: (m1_subset_1('#skF_3'('#skF_5', '#skF_6', C_915, '#skF_8'), '#skF_5') | r2_relset_1('#skF_5', '#skF_6', C_915, '#skF_8') | ~m1_subset_1(C_915, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_66, c_5360])).
% 9.41/3.29  tff(c_5448, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_6', '#skF_8', '#skF_8'), '#skF_5') | r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_66, c_5438])).
% 9.41/3.29  tff(c_5449, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(splitLeft, [status(thm)], [c_5448])).
% 9.41/3.29  tff(c_5091, plain, (![B_871, A_872, C_873]: (k1_xboole_0=B_871 | k1_relset_1(A_872, B_871, C_873)=A_872 | ~v1_funct_2(C_873, A_872, B_871) | ~m1_subset_1(C_873, k1_zfmisc_1(k2_zfmisc_1(A_872, B_871))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.41/3.29  tff(c_5094, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_72, c_5091])).
% 9.41/3.29  tff(c_5106, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4946, c_5094])).
% 9.41/3.29  tff(c_5111, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_5106])).
% 9.41/3.29  tff(c_165, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_153])).
% 9.41/3.29  tff(c_70, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.41/3.29  tff(c_68, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.41/3.29  tff(c_4947, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_4933])).
% 9.41/3.29  tff(c_5097, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_5091])).
% 9.41/3.29  tff(c_5109, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4947, c_5097])).
% 9.41/3.29  tff(c_5117, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_5109])).
% 9.41/3.29  tff(c_5242, plain, (![A_891, B_892]: (r2_hidden('#skF_2'(A_891, B_892), k1_relat_1(A_891)) | B_892=A_891 | k1_relat_1(B_892)!=k1_relat_1(A_891) | ~v1_funct_1(B_892) | ~v1_relat_1(B_892) | ~v1_funct_1(A_891) | ~v1_relat_1(A_891))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.41/3.29  tff(c_5252, plain, (![B_892]: (r2_hidden('#skF_2'('#skF_8', B_892), '#skF_5') | B_892='#skF_8' | k1_relat_1(B_892)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_892) | ~v1_relat_1(B_892) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5117, c_5242])).
% 9.41/3.29  tff(c_5264, plain, (![B_895]: (r2_hidden('#skF_2'('#skF_8', B_895), '#skF_5') | B_895='#skF_8' | k1_relat_1(B_895)!='#skF_5' | ~v1_funct_1(B_895) | ~v1_relat_1(B_895))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_70, c_5117, c_5252])).
% 9.41/3.29  tff(c_64, plain, (![E_63]: (k1_funct_1('#skF_7', E_63)=k1_funct_1('#skF_8', E_63) | ~r2_hidden(E_63, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.41/3.29  tff(c_5818, plain, (![B_988]: (k1_funct_1('#skF_7', '#skF_2'('#skF_8', B_988))=k1_funct_1('#skF_8', '#skF_2'('#skF_8', B_988)) | B_988='#skF_8' | k1_relat_1(B_988)!='#skF_5' | ~v1_funct_1(B_988) | ~v1_relat_1(B_988))), inference(resolution, [status(thm)], [c_5264, c_64])).
% 9.41/3.29  tff(c_24, plain, (![B_19, A_15]: (k1_funct_1(B_19, '#skF_2'(A_15, B_19))!=k1_funct_1(A_15, '#skF_2'(A_15, B_19)) | B_19=A_15 | k1_relat_1(B_19)!=k1_relat_1(A_15) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.41/3.29  tff(c_5825, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5818, c_24])).
% 9.41/3.29  tff(c_5832, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_5111, c_165, c_70, c_5117, c_5111, c_5825])).
% 9.41/3.29  tff(c_62, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.41/3.29  tff(c_5868, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5832, c_62])).
% 9.41/3.29  tff(c_5880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5449, c_5868])).
% 9.41/3.29  tff(c_5882, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(splitRight, [status(thm)], [c_5448])).
% 9.41/3.29  tff(c_42, plain, (![A_26, B_27, C_28, D_42]: (r2_hidden(k4_tarski('#skF_3'(A_26, B_27, C_28, D_42), '#skF_4'(A_26, B_27, C_28, D_42)), C_28) | r2_hidden(k4_tarski('#skF_3'(A_26, B_27, C_28, D_42), '#skF_4'(A_26, B_27, C_28, D_42)), D_42) | r2_relset_1(A_26, B_27, C_28, D_42) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.41/3.29  tff(c_7317, plain, (![A_26, B_27, D_42]: (r2_relset_1(A_26, B_27, D_42, D_42) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | r2_hidden(k4_tarski('#skF_3'(A_26, B_27, D_42, D_42), '#skF_4'(A_26, B_27, D_42, D_42)), D_42))), inference(factorization, [status(thm), theory('equality')], [c_42])).
% 9.41/3.29  tff(c_8035, plain, (![A_1315, B_1316, D_1317]: (r2_relset_1(A_1315, B_1316, D_1317, D_1317) | ~m1_subset_1(D_1317, k1_zfmisc_1(k2_zfmisc_1(A_1315, B_1316))) | r2_hidden(k4_tarski('#skF_3'(A_1315, B_1316, D_1317, D_1317), '#skF_4'(A_1315, B_1316, D_1317, D_1317)), D_1317))), inference(factorization, [status(thm), theory('equality')], [c_42])).
% 9.41/3.29  tff(c_36, plain, (![A_26, B_27, C_28, D_42]: (~r2_hidden(k4_tarski('#skF_3'(A_26, B_27, C_28, D_42), '#skF_4'(A_26, B_27, C_28, D_42)), D_42) | ~r2_hidden(k4_tarski('#skF_3'(A_26, B_27, C_28, D_42), '#skF_4'(A_26, B_27, C_28, D_42)), C_28) | r2_relset_1(A_26, B_27, C_28, D_42) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.41/3.29  tff(c_8115, plain, (![A_1332, B_1333, D_1334]: (~r2_hidden(k4_tarski('#skF_3'(A_1332, B_1333, D_1334, D_1334), '#skF_4'(A_1332, B_1333, D_1334, D_1334)), D_1334) | r2_relset_1(A_1332, B_1333, D_1334, D_1334) | ~m1_subset_1(D_1334, k1_zfmisc_1(k2_zfmisc_1(A_1332, B_1333))))), inference(resolution, [status(thm)], [c_8035, c_36])).
% 9.41/3.29  tff(c_8124, plain, (![A_1335, B_1336, D_1337]: (r2_relset_1(A_1335, B_1336, D_1337, D_1337) | ~m1_subset_1(D_1337, k1_zfmisc_1(k2_zfmisc_1(A_1335, B_1336))))), inference(resolution, [status(thm)], [c_7317, c_8115])).
% 9.41/3.29  tff(c_8132, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_66, c_8124])).
% 9.41/3.29  tff(c_8142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5882, c_8132])).
% 9.41/3.29  tff(c_8143, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_5109])).
% 9.41/3.29  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.41/3.29  tff(c_8168, plain, (![A_8]: (r1_tarski('#skF_6', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_8143, c_14])).
% 9.41/3.29  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.41/3.29  tff(c_8166, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8143, c_8143, c_18])).
% 9.41/3.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.41/3.29  tff(c_184, plain, (![C_89, A_90, B_91]: (r2_hidden(C_89, A_90) | ~r2_hidden(C_89, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.41/3.29  tff(c_5015, plain, (![A_853, B_854, A_855]: (r2_hidden('#skF_1'(A_853, B_854), A_855) | ~m1_subset_1(A_853, k1_zfmisc_1(A_855)) | r1_tarski(A_853, B_854))), inference(resolution, [status(thm)], [c_6, c_184])).
% 9.41/3.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.41/3.29  tff(c_5036, plain, (![A_856, A_857]: (~m1_subset_1(A_856, k1_zfmisc_1(A_857)) | r1_tarski(A_856, A_857))), inference(resolution, [status(thm)], [c_5015, c_4])).
% 9.41/3.29  tff(c_5049, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_5036])).
% 9.41/3.29  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.41/3.29  tff(c_5060, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_8' | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_8')), inference(resolution, [status(thm)], [c_5049, c_8])).
% 9.41/3.29  tff(c_5064, plain, (~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_5060])).
% 9.41/3.29  tff(c_8207, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8166, c_5064])).
% 9.41/3.29  tff(c_8215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8168, c_8207])).
% 9.41/3.29  tff(c_8216, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_5106])).
% 9.41/3.29  tff(c_8237, plain, (![A_8]: (r1_tarski('#skF_6', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_8216, c_14])).
% 9.41/3.29  tff(c_8235, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8216, c_8216, c_18])).
% 9.41/3.29  tff(c_8296, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8235, c_5064])).
% 9.41/3.29  tff(c_8304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8237, c_8296])).
% 9.41/3.29  tff(c_8305, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_8'), inference(splitRight, [status(thm)], [c_5060])).
% 9.41/3.29  tff(c_8310, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_8305, c_72])).
% 9.41/3.29  tff(c_8425, plain, (![B_1367, A_1368, C_1369]: (k1_xboole_0=B_1367 | k1_relset_1(A_1368, B_1367, C_1369)=A_1368 | ~v1_funct_2(C_1369, A_1368, B_1367) | ~m1_subset_1(C_1369, k1_zfmisc_1(k2_zfmisc_1(A_1368, B_1367))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.41/3.29  tff(c_8428, plain, (![C_1369]: (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', C_1369)='#skF_5' | ~v1_funct_2(C_1369, '#skF_5', '#skF_6') | ~m1_subset_1(C_1369, k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_8305, c_8425])).
% 9.41/3.29  tff(c_8538, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_8428])).
% 9.41/3.29  tff(c_16, plain, (![B_10, A_9]: (k1_xboole_0=B_10 | k1_xboole_0=A_9 | k2_zfmisc_1(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.41/3.29  tff(c_8321, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_8305, c_16])).
% 9.41/3.29  tff(c_8359, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_8321])).
% 9.41/3.29  tff(c_8543, plain, ('#skF_6'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8538, c_8359])).
% 9.41/3.29  tff(c_8623, plain, (![A_1402]: (k2_zfmisc_1(A_1402, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8538, c_8538, c_18])).
% 9.41/3.29  tff(c_8632, plain, ('#skF_6'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_8623, c_8305])).
% 9.41/3.29  tff(c_8649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8543, c_8632])).
% 9.41/3.29  tff(c_8652, plain, (![C_1403]: (k1_relset_1('#skF_5', '#skF_6', C_1403)='#skF_5' | ~v1_funct_2(C_1403, '#skF_5', '#skF_6') | ~m1_subset_1(C_1403, k1_zfmisc_1('#skF_8')))), inference(splitRight, [status(thm)], [c_8428])).
% 9.41/3.29  tff(c_8658, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_8310, c_8652])).
% 9.41/3.29  tff(c_8664, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4946, c_8658])).
% 9.41/3.29  tff(c_8311, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_8305, c_66])).
% 9.41/3.29  tff(c_8655, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_8311, c_8652])).
% 9.41/3.29  tff(c_8661, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4947, c_8655])).
% 9.41/3.29  tff(c_26, plain, (![A_15, B_19]: (r2_hidden('#skF_2'(A_15, B_19), k1_relat_1(A_15)) | B_19=A_15 | k1_relat_1(B_19)!=k1_relat_1(A_15) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.41/3.29  tff(c_8669, plain, (![B_19]: (r2_hidden('#skF_2'('#skF_8', B_19), '#skF_5') | B_19='#skF_8' | k1_relat_1(B_19)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8661, c_26])).
% 9.41/3.29  tff(c_8717, plain, (![B_1409]: (r2_hidden('#skF_2'('#skF_8', B_1409), '#skF_5') | B_1409='#skF_8' | k1_relat_1(B_1409)!='#skF_5' | ~v1_funct_1(B_1409) | ~v1_relat_1(B_1409))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_70, c_8661, c_8669])).
% 9.41/3.29  tff(c_8889, plain, (![B_1447]: (k1_funct_1('#skF_7', '#skF_2'('#skF_8', B_1447))=k1_funct_1('#skF_8', '#skF_2'('#skF_8', B_1447)) | B_1447='#skF_8' | k1_relat_1(B_1447)!='#skF_5' | ~v1_funct_1(B_1447) | ~v1_relat_1(B_1447))), inference(resolution, [status(thm)], [c_8717, c_64])).
% 9.41/3.29  tff(c_8896, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_8889, c_24])).
% 9.41/3.29  tff(c_8903, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_8664, c_165, c_70, c_8664, c_8661, c_8896])).
% 9.41/3.29  tff(c_5048, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_5036])).
% 9.41/3.29  tff(c_5057, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_7' | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_5048, c_8])).
% 9.41/3.29  tff(c_5063, plain, (~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_5057])).
% 9.41/3.29  tff(c_8307, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8305, c_5063])).
% 9.41/3.29  tff(c_8929, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8903, c_8307])).
% 9.41/3.29  tff(c_8944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8929])).
% 9.41/3.29  tff(c_8946, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_8321])).
% 9.41/3.29  tff(c_8964, plain, (![A_8]: (r1_tarski('#skF_8', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_8946, c_14])).
% 9.41/3.29  tff(c_8973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8964, c_8307])).
% 9.41/3.29  tff(c_8974, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_5057])).
% 9.41/3.29  tff(c_8978, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_8974, c_72])).
% 9.41/3.29  tff(c_9030, plain, (![B_1451, C_1452, A_1453]: (k1_xboole_0=B_1451 | v1_funct_2(C_1452, A_1453, B_1451) | k1_relset_1(A_1453, B_1451, C_1452)!=A_1453 | ~m1_subset_1(C_1452, k1_zfmisc_1(k2_zfmisc_1(A_1453, B_1451))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.41/3.29  tff(c_9033, plain, (![C_1452]: (k1_xboole_0='#skF_6' | v1_funct_2(C_1452, '#skF_5', '#skF_6') | k1_relset_1('#skF_5', '#skF_6', C_1452)!='#skF_5' | ~m1_subset_1(C_1452, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_8974, c_9030])).
% 9.41/3.29  tff(c_9068, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_9033])).
% 9.41/3.29  tff(c_8989, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_8974, c_16])).
% 9.41/3.29  tff(c_9029, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_8989])).
% 9.41/3.29  tff(c_9071, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9068, c_9029])).
% 9.41/3.29  tff(c_9087, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9068, c_9068, c_18])).
% 9.41/3.29  tff(c_9120, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9087, c_8974])).
% 9.41/3.29  tff(c_9122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9071, c_9120])).
% 9.41/3.29  tff(c_9124, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_9033])).
% 9.41/3.29  tff(c_9180, plain, (![B_1477, A_1478, C_1479]: (k1_xboole_0=B_1477 | k1_relset_1(A_1478, B_1477, C_1479)=A_1478 | ~v1_funct_2(C_1479, A_1478, B_1477) | ~m1_subset_1(C_1479, k1_zfmisc_1(k2_zfmisc_1(A_1478, B_1477))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.41/3.29  tff(c_9183, plain, (![C_1479]: (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', C_1479)='#skF_5' | ~v1_funct_2(C_1479, '#skF_5', '#skF_6') | ~m1_subset_1(C_1479, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_8974, c_9180])).
% 9.41/3.29  tff(c_9192, plain, (![C_1480]: (k1_relset_1('#skF_5', '#skF_6', C_1480)='#skF_5' | ~v1_funct_2(C_1480, '#skF_5', '#skF_6') | ~m1_subset_1(C_1480, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_9124, c_9183])).
% 9.41/3.29  tff(c_9198, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_8978, c_9192])).
% 9.41/3.29  tff(c_9204, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4946, c_9198])).
% 9.41/3.29  tff(c_8979, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_8974, c_66])).
% 9.41/3.29  tff(c_9195, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_8979, c_9192])).
% 9.41/3.29  tff(c_9201, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4947, c_9195])).
% 9.41/3.29  tff(c_9278, plain, (![A_1492, B_1493]: (r2_hidden('#skF_2'(A_1492, B_1493), k1_relat_1(A_1492)) | B_1493=A_1492 | k1_relat_1(B_1493)!=k1_relat_1(A_1492) | ~v1_funct_1(B_1493) | ~v1_relat_1(B_1493) | ~v1_funct_1(A_1492) | ~v1_relat_1(A_1492))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.41/3.29  tff(c_9291, plain, (![B_1493]: (r2_hidden('#skF_2'('#skF_8', B_1493), '#skF_5') | B_1493='#skF_8' | k1_relat_1(B_1493)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_1493) | ~v1_relat_1(B_1493) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9201, c_9278])).
% 9.41/3.29  tff(c_9316, plain, (![B_1495]: (r2_hidden('#skF_2'('#skF_8', B_1495), '#skF_5') | B_1495='#skF_8' | k1_relat_1(B_1495)!='#skF_5' | ~v1_funct_1(B_1495) | ~v1_relat_1(B_1495))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_70, c_9201, c_9291])).
% 9.41/3.29  tff(c_9329, plain, (![B_1495]: (k1_funct_1('#skF_7', '#skF_2'('#skF_8', B_1495))=k1_funct_1('#skF_8', '#skF_2'('#skF_8', B_1495)) | B_1495='#skF_8' | k1_relat_1(B_1495)!='#skF_5' | ~v1_funct_1(B_1495) | ~v1_relat_1(B_1495))), inference(resolution, [status(thm)], [c_9316, c_64])).
% 9.41/3.29  tff(c_9539, plain, (![B_1549, A_1550]: (k1_funct_1(B_1549, '#skF_2'(A_1550, B_1549))!=k1_funct_1(A_1550, '#skF_2'(A_1550, B_1549)) | B_1549=A_1550 | k1_relat_1(B_1549)!=k1_relat_1(A_1550) | ~v1_funct_1(B_1549) | ~v1_relat_1(B_1549) | ~v1_funct_1(A_1550) | ~v1_relat_1(A_1550))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.41/3.29  tff(c_9543, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_9329, c_9539])).
% 9.41/3.29  tff(c_9549, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_9204, c_165, c_70, c_9204, c_9201, c_9543])).
% 9.41/3.29  tff(c_9016, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8974, c_8974, c_5060])).
% 9.41/3.29  tff(c_9017, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_9016])).
% 9.41/3.29  tff(c_9586, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9549, c_9017])).
% 9.41/3.29  tff(c_9603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_9586])).
% 9.41/3.29  tff(c_9605, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_8989])).
% 9.41/3.29  tff(c_9623, plain, (![A_8]: (r1_tarski('#skF_7', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_9605, c_14])).
% 9.41/3.29  tff(c_9632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9623, c_9017])).
% 9.41/3.29  tff(c_9633, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_9016])).
% 9.41/3.29  tff(c_9673, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9633, c_62])).
% 9.41/3.29  tff(c_9663, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9633, c_8979])).
% 9.41/3.29  tff(c_9666, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9633, c_8974])).
% 9.41/3.29  tff(c_10475, plain, (![A_26, B_27, C_28]: (r2_relset_1(A_26, B_27, C_28, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | r2_hidden(k4_tarski('#skF_3'(A_26, B_27, C_28, C_28), '#skF_4'(A_26, B_27, C_28, C_28)), C_28))), inference(factorization, [status(thm), theory('equality')], [c_42])).
% 9.41/3.29  tff(c_10566, plain, (![A_1706, B_1707, C_1708, D_1709]: (~r2_hidden(k4_tarski('#skF_3'(A_1706, B_1707, C_1708, D_1709), '#skF_4'(A_1706, B_1707, C_1708, D_1709)), D_1709) | ~r2_hidden(k4_tarski('#skF_3'(A_1706, B_1707, C_1708, D_1709), '#skF_4'(A_1706, B_1707, C_1708, D_1709)), C_1708) | r2_relset_1(A_1706, B_1707, C_1708, D_1709) | ~m1_subset_1(D_1709, k1_zfmisc_1(k2_zfmisc_1(A_1706, B_1707))) | ~m1_subset_1(C_1708, k1_zfmisc_1(k2_zfmisc_1(A_1706, B_1707))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.41/3.29  tff(c_10574, plain, (![A_1710, B_1711, C_1712]: (~r2_hidden(k4_tarski('#skF_3'(A_1710, B_1711, C_1712, C_1712), '#skF_4'(A_1710, B_1711, C_1712, C_1712)), C_1712) | r2_relset_1(A_1710, B_1711, C_1712, C_1712) | ~m1_subset_1(C_1712, k1_zfmisc_1(k2_zfmisc_1(A_1710, B_1711))))), inference(resolution, [status(thm)], [c_10475, c_10566])).
% 9.41/3.29  tff(c_10583, plain, (![A_1713, B_1714, C_1715]: (r2_relset_1(A_1713, B_1714, C_1715, C_1715) | ~m1_subset_1(C_1715, k1_zfmisc_1(k2_zfmisc_1(A_1713, B_1714))))), inference(resolution, [status(thm)], [c_10475, c_10574])).
% 9.41/3.29  tff(c_10598, plain, (![C_1716]: (r2_relset_1('#skF_5', '#skF_6', C_1716, C_1716) | ~m1_subset_1(C_1716, k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_9666, c_10583])).
% 9.41/3.29  tff(c_10606, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_9663, c_10598])).
% 9.41/3.29  tff(c_10612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9673, c_10606])).
% 9.41/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.29  
% 9.41/3.29  Inference rules
% 9.41/3.29  ----------------------
% 9.41/3.29  #Ref     : 17
% 9.41/3.29  #Sup     : 2211
% 9.41/3.29  #Fact    : 8
% 9.41/3.29  #Define  : 0
% 9.41/3.29  #Split   : 79
% 9.41/3.29  #Chain   : 0
% 9.41/3.29  #Close   : 0
% 9.41/3.29  
% 9.41/3.29  Ordering : KBO
% 9.41/3.29  
% 9.41/3.29  Simplification rules
% 9.41/3.29  ----------------------
% 9.41/3.29  #Subsume      : 766
% 9.41/3.29  #Demod        : 1883
% 9.41/3.29  #Tautology    : 569
% 9.41/3.29  #SimpNegUnit  : 44
% 9.41/3.29  #BackRed      : 778
% 9.41/3.29  
% 9.41/3.29  #Partial instantiations: 0
% 9.41/3.29  #Strategies tried      : 1
% 9.41/3.29  
% 9.41/3.29  Timing (in seconds)
% 9.41/3.29  ----------------------
% 9.41/3.29  Preprocessing        : 0.35
% 9.41/3.29  Parsing              : 0.18
% 9.41/3.29  CNF conversion       : 0.03
% 9.41/3.29  Main loop            : 2.14
% 9.41/3.29  Inferencing          : 0.66
% 9.41/3.29  Reduction            : 0.63
% 9.41/3.29  Demodulation         : 0.42
% 9.41/3.29  BG Simplification    : 0.07
% 9.41/3.29  Subsumption          : 0.62
% 9.41/3.29  Abstraction          : 0.08
% 9.41/3.29  MUC search           : 0.00
% 9.41/3.29  Cooper               : 0.00
% 9.41/3.29  Total                : 2.55
% 9.41/3.29  Index Insertion      : 0.00
% 9.41/3.29  Index Deletion       : 0.00
% 9.41/3.29  Index Matching       : 0.00
% 9.41/3.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
