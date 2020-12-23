%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:43 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 448 expanded)
%              Number of leaves         :   36 ( 162 expanded)
%              Depth                    :   15
%              Number of atoms          :  291 (1403 expanded)
%              Number of equality atoms :   63 ( 303 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_24,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_108,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_114,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_108])).

tff(c_118,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_114])).

tff(c_166,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_175,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_166])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_70,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_345,plain,(
    ! [A_97] :
      ( r2_hidden('#skF_1'(A_97),k1_relat_1(A_97))
      | v2_funct_1(A_97)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [C_7,A_4,B_5] :
      ( r2_hidden(C_7,A_4)
      | ~ r2_hidden(C_7,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1005,plain,(
    ! [A_173,A_174] :
      ( r2_hidden('#skF_1'(A_173),A_174)
      | ~ m1_subset_1(k1_relat_1(A_173),k1_zfmisc_1(A_174))
      | v2_funct_1(A_173)
      | ~ v1_funct_1(A_173)
      | ~ v1_relat_1(A_173) ) ),
    inference(resolution,[status(thm)],[c_345,c_10])).

tff(c_1404,plain,(
    ! [A_216,B_217] :
      ( r2_hidden('#skF_1'(A_216),B_217)
      | v2_funct_1(A_216)
      | ~ v1_funct_1(A_216)
      | ~ v1_relat_1(A_216)
      | ~ r1_tarski(k1_relat_1(A_216),B_217) ) ),
    inference(resolution,[status(thm)],[c_14,c_1005])).

tff(c_303,plain,(
    ! [A_84] :
      ( '#skF_2'(A_84) != '#skF_1'(A_84)
      | v2_funct_1(A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_306,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_303,c_70])).

tff(c_309,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_46,c_306])).

tff(c_369,plain,(
    ! [A_100] :
      ( r2_hidden('#skF_2'(A_100),k1_relat_1(A_100))
      | v2_funct_1(A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_861,plain,(
    ! [A_156,A_157] :
      ( r2_hidden('#skF_2'(A_156),A_157)
      | ~ m1_subset_1(k1_relat_1(A_156),k1_zfmisc_1(A_157))
      | v2_funct_1(A_156)
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(resolution,[status(thm)],[c_369,c_10])).

tff(c_877,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_2'(A_158),B_159)
      | v2_funct_1(A_158)
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158)
      | ~ r1_tarski(k1_relat_1(A_158),B_159) ) ),
    inference(resolution,[status(thm)],[c_14,c_861])).

tff(c_442,plain,(
    ! [A_113] :
      ( k1_funct_1(A_113,'#skF_2'(A_113)) = k1_funct_1(A_113,'#skF_1'(A_113))
      | v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    ! [D_39,C_38] :
      ( v2_funct_1('#skF_4')
      | D_39 = C_38
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4',C_38)
      | ~ r2_hidden(D_39,'#skF_3')
      | ~ r2_hidden(C_38,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_273,plain,(
    ! [D_39,C_38] :
      ( D_39 = C_38
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4',C_38)
      | ~ r2_hidden(D_39,'#skF_3')
      | ~ r2_hidden(C_38,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66])).

tff(c_448,plain,(
    ! [C_38] :
      ( C_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_38,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_273])).

tff(c_457,plain,(
    ! [C_38] :
      ( C_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_38,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_46,c_448])).

tff(c_458,plain,(
    ! [C_38] :
      ( C_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_38,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_457])).

tff(c_671,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_458])).

tff(c_882,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_877,c_671])).

tff(c_890,plain,
    ( v2_funct_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_46,c_882])).

tff(c_891,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_890])).

tff(c_896,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_891])).

tff(c_900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_175,c_896])).

tff(c_902,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_451,plain,(
    ! [D_39] :
      ( D_39 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_39,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_273])).

tff(c_460,plain,(
    ! [D_39] :
      ( D_39 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_39,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_46,c_451])).

tff(c_461,plain,(
    ! [D_39] :
      ( D_39 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_39,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_460])).

tff(c_910,plain,(
    ! [D_39] :
      ( D_39 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_39,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_461])).

tff(c_913,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_910])).

tff(c_914,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_913])).

tff(c_1415,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1404,c_914])).

tff(c_1425,plain,
    ( v2_funct_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_46,c_1415])).

tff(c_1426,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1425])).

tff(c_1431,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1426])).

tff(c_1435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_175,c_1431])).

tff(c_1436,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1437,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1454,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_50])).

tff(c_54,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1442,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_54])).

tff(c_2078,plain,(
    ! [D_322,C_323,B_324,A_325] :
      ( k1_funct_1(k2_funct_1(D_322),k1_funct_1(D_322,C_323)) = C_323
      | k1_xboole_0 = B_324
      | ~ r2_hidden(C_323,A_325)
      | ~ v2_funct_1(D_322)
      | ~ m1_subset_1(D_322,k1_zfmisc_1(k2_zfmisc_1(A_325,B_324)))
      | ~ v1_funct_2(D_322,A_325,B_324)
      | ~ v1_funct_1(D_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2155,plain,(
    ! [D_330,B_331] :
      ( k1_funct_1(k2_funct_1(D_330),k1_funct_1(D_330,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_331
      | ~ v2_funct_1(D_330)
      | ~ m1_subset_1(D_330,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_331)))
      | ~ v1_funct_2(D_330,'#skF_3',B_331)
      | ~ v1_funct_1(D_330) ) ),
    inference(resolution,[status(thm)],[c_1442,c_2078])).

tff(c_2166,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2155])).

tff(c_2172,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1437,c_1454,c_2166])).

tff(c_2173,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2172])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1440,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_52])).

tff(c_1676,plain,(
    ! [C_259,A_260,B_261] :
      ( r2_hidden(C_259,A_260)
      | ~ r2_hidden(C_259,B_261)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(A_260)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1694,plain,(
    ! [A_264] :
      ( r2_hidden('#skF_6',A_264)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_264)) ) ),
    inference(resolution,[status(thm)],[c_1440,c_1676])).

tff(c_1699,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_6',B_9)
      | ~ r1_tarski('#skF_3',B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_1694])).

tff(c_1704,plain,(
    ! [A_266,C_267,B_268] :
      ( m1_subset_1(A_266,C_267)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(C_267))
      | ~ r2_hidden(A_266,B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1727,plain,(
    ! [A_271,B_272,A_273] :
      ( m1_subset_1(A_271,B_272)
      | ~ r2_hidden(A_271,A_273)
      | ~ r1_tarski(A_273,B_272) ) ),
    inference(resolution,[status(thm)],[c_14,c_1704])).

tff(c_1756,plain,(
    ! [B_276,B_277] :
      ( m1_subset_1('#skF_6',B_276)
      | ~ r1_tarski(B_277,B_276)
      | ~ r1_tarski('#skF_3',B_277) ) ),
    inference(resolution,[status(thm)],[c_1699,c_1727])).

tff(c_1768,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_6',A_3)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1756])).

tff(c_1786,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1768])).

tff(c_2177,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_1786])).

tff(c_2190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2177])).

tff(c_2192,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2172])).

tff(c_2191,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2172])).

tff(c_2305,plain,(
    ! [D_340,B_341] :
      ( k1_funct_1(k2_funct_1(D_340),k1_funct_1(D_340,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_341
      | ~ v2_funct_1(D_340)
      | ~ m1_subset_1(D_340,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_341)))
      | ~ v1_funct_2(D_340,'#skF_3',B_341)
      | ~ v1_funct_1(D_340) ) ),
    inference(resolution,[status(thm)],[c_1440,c_2078])).

tff(c_2322,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2305])).

tff(c_2330,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1437,c_2191,c_2322])).

tff(c_2332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2192,c_1436,c_2330])).

tff(c_2334,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1768])).

tff(c_1459,plain,(
    ! [B_224,A_225] :
      ( B_224 = A_225
      | ~ r1_tarski(B_224,A_225)
      | ~ r1_tarski(A_225,B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1471,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1459])).

tff(c_2378,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2334,c_1471])).

tff(c_2392,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2378,c_8])).

tff(c_2416,plain,(
    ! [B_9] : r2_hidden('#skF_6',B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_1699])).

tff(c_1683,plain,(
    ! [A_262] :
      ( r2_hidden('#skF_5',A_262)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_262)) ) ),
    inference(resolution,[status(thm)],[c_1442,c_1676])).

tff(c_1688,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_5',B_9)
      | ~ r1_tarski('#skF_3',B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_1683])).

tff(c_2418,plain,(
    ! [B_9] : r2_hidden('#skF_5',B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_1688])).

tff(c_1485,plain,(
    ! [B_227,A_228] :
      ( v1_relat_1(B_227)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(A_228))
      | ~ v1_relat_1(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1491,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_1485])).

tff(c_1495,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1491])).

tff(c_2464,plain,(
    ! [C_350,B_351,A_352] :
      ( C_350 = B_351
      | k1_funct_1(A_352,C_350) != k1_funct_1(A_352,B_351)
      | ~ r2_hidden(C_350,k1_relat_1(A_352))
      | ~ r2_hidden(B_351,k1_relat_1(A_352))
      | ~ v2_funct_1(A_352)
      | ~ v1_funct_1(A_352)
      | ~ v1_relat_1(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2472,plain,(
    ! [C_350] :
      ( C_350 = '#skF_5'
      | k1_funct_1('#skF_4',C_350) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_350,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1454,c_2464])).

tff(c_2476,plain,(
    ! [C_350] :
      ( C_350 = '#skF_5'
      | k1_funct_1('#skF_4',C_350) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_350,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_46,c_1437,c_2472])).

tff(c_2527,plain,(
    ! [C_356] :
      ( C_356 = '#skF_5'
      | k1_funct_1('#skF_4',C_356) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_356,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2476])).

tff(c_2531,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2416,c_2527])).

tff(c_2547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1436,c_2531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.80  
% 4.55/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.80  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.55/1.80  
% 4.55/1.80  %Foreground sorts:
% 4.55/1.80  
% 4.55/1.80  
% 4.55/1.80  %Background operators:
% 4.55/1.80  
% 4.55/1.80  
% 4.55/1.80  %Foreground operators:
% 4.55/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.80  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.55/1.80  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.55/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.80  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.55/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.55/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.55/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.80  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.55/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.55/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.80  
% 4.71/1.82  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.71/1.82  tff(f_118, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 4.71/1.82  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.71/1.82  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.71/1.82  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.71/1.82  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.71/1.82  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 4.71/1.82  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.71/1.82  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.71/1.82  tff(f_100, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 4.71/1.82  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.71/1.82  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.71/1.82  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.71/1.82  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.82  tff(c_108, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.71/1.82  tff(c_114, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_108])).
% 4.71/1.82  tff(c_118, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_114])).
% 4.71/1.82  tff(c_166, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.71/1.82  tff(c_175, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_166])).
% 4.71/1.82  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.71/1.82  tff(c_48, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.82  tff(c_70, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 4.71/1.82  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.82  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.71/1.82  tff(c_345, plain, (![A_97]: (r2_hidden('#skF_1'(A_97), k1_relat_1(A_97)) | v2_funct_1(A_97) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.71/1.82  tff(c_10, plain, (![C_7, A_4, B_5]: (r2_hidden(C_7, A_4) | ~r2_hidden(C_7, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.71/1.82  tff(c_1005, plain, (![A_173, A_174]: (r2_hidden('#skF_1'(A_173), A_174) | ~m1_subset_1(k1_relat_1(A_173), k1_zfmisc_1(A_174)) | v2_funct_1(A_173) | ~v1_funct_1(A_173) | ~v1_relat_1(A_173))), inference(resolution, [status(thm)], [c_345, c_10])).
% 4.71/1.82  tff(c_1404, plain, (![A_216, B_217]: (r2_hidden('#skF_1'(A_216), B_217) | v2_funct_1(A_216) | ~v1_funct_1(A_216) | ~v1_relat_1(A_216) | ~r1_tarski(k1_relat_1(A_216), B_217))), inference(resolution, [status(thm)], [c_14, c_1005])).
% 4.71/1.82  tff(c_303, plain, (![A_84]: ('#skF_2'(A_84)!='#skF_1'(A_84) | v2_funct_1(A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.71/1.82  tff(c_306, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_303, c_70])).
% 4.71/1.82  tff(c_309, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_46, c_306])).
% 4.71/1.82  tff(c_369, plain, (![A_100]: (r2_hidden('#skF_2'(A_100), k1_relat_1(A_100)) | v2_funct_1(A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.71/1.82  tff(c_861, plain, (![A_156, A_157]: (r2_hidden('#skF_2'(A_156), A_157) | ~m1_subset_1(k1_relat_1(A_156), k1_zfmisc_1(A_157)) | v2_funct_1(A_156) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(resolution, [status(thm)], [c_369, c_10])).
% 4.71/1.82  tff(c_877, plain, (![A_158, B_159]: (r2_hidden('#skF_2'(A_158), B_159) | v2_funct_1(A_158) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158) | ~r1_tarski(k1_relat_1(A_158), B_159))), inference(resolution, [status(thm)], [c_14, c_861])).
% 4.71/1.82  tff(c_442, plain, (![A_113]: (k1_funct_1(A_113, '#skF_2'(A_113))=k1_funct_1(A_113, '#skF_1'(A_113)) | v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.71/1.82  tff(c_66, plain, (![D_39, C_38]: (v2_funct_1('#skF_4') | D_39=C_38 | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', C_38) | ~r2_hidden(D_39, '#skF_3') | ~r2_hidden(C_38, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.82  tff(c_273, plain, (![D_39, C_38]: (D_39=C_38 | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', C_38) | ~r2_hidden(D_39, '#skF_3') | ~r2_hidden(C_38, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_66])).
% 4.71/1.82  tff(c_448, plain, (![C_38]: (C_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_38, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_273])).
% 4.71/1.82  tff(c_457, plain, (![C_38]: (C_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_38, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_46, c_448])).
% 4.71/1.82  tff(c_458, plain, (![C_38]: (C_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_38, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_457])).
% 4.71/1.82  tff(c_671, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_458])).
% 4.71/1.82  tff(c_882, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_877, c_671])).
% 4.71/1.82  tff(c_890, plain, (v2_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_46, c_882])).
% 4.71/1.82  tff(c_891, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_890])).
% 4.71/1.82  tff(c_896, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_891])).
% 4.71/1.82  tff(c_900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_175, c_896])).
% 4.71/1.82  tff(c_902, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_458])).
% 4.71/1.82  tff(c_451, plain, (![D_39]: (D_39='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_39, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_273])).
% 4.71/1.82  tff(c_460, plain, (![D_39]: (D_39='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_39, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_46, c_451])).
% 4.71/1.82  tff(c_461, plain, (![D_39]: (D_39='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_39, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_460])).
% 4.71/1.82  tff(c_910, plain, (![D_39]: (D_39='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_39, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_902, c_461])).
% 4.71/1.82  tff(c_913, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_910])).
% 4.71/1.82  tff(c_914, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_309, c_913])).
% 4.71/1.82  tff(c_1415, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1404, c_914])).
% 4.71/1.82  tff(c_1425, plain, (v2_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_46, c_1415])).
% 4.71/1.82  tff(c_1426, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_1425])).
% 4.71/1.82  tff(c_1431, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1426])).
% 4.71/1.82  tff(c_1435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_175, c_1431])).
% 4.71/1.82  tff(c_1436, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 4.71/1.82  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.71/1.82  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.82  tff(c_1437, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 4.71/1.82  tff(c_50, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.82  tff(c_1454, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_50])).
% 4.71/1.82  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.82  tff(c_1442, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_54])).
% 4.71/1.82  tff(c_2078, plain, (![D_322, C_323, B_324, A_325]: (k1_funct_1(k2_funct_1(D_322), k1_funct_1(D_322, C_323))=C_323 | k1_xboole_0=B_324 | ~r2_hidden(C_323, A_325) | ~v2_funct_1(D_322) | ~m1_subset_1(D_322, k1_zfmisc_1(k2_zfmisc_1(A_325, B_324))) | ~v1_funct_2(D_322, A_325, B_324) | ~v1_funct_1(D_322))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.71/1.82  tff(c_2155, plain, (![D_330, B_331]: (k1_funct_1(k2_funct_1(D_330), k1_funct_1(D_330, '#skF_5'))='#skF_5' | k1_xboole_0=B_331 | ~v2_funct_1(D_330) | ~m1_subset_1(D_330, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_331))) | ~v1_funct_2(D_330, '#skF_3', B_331) | ~v1_funct_1(D_330))), inference(resolution, [status(thm)], [c_1442, c_2078])).
% 4.71/1.82  tff(c_2166, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_2155])).
% 4.71/1.82  tff(c_2172, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1437, c_1454, c_2166])).
% 4.71/1.82  tff(c_2173, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2172])).
% 4.71/1.82  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.71/1.82  tff(c_52, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.82  tff(c_1440, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_52])).
% 4.71/1.82  tff(c_1676, plain, (![C_259, A_260, B_261]: (r2_hidden(C_259, A_260) | ~r2_hidden(C_259, B_261) | ~m1_subset_1(B_261, k1_zfmisc_1(A_260)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.71/1.82  tff(c_1694, plain, (![A_264]: (r2_hidden('#skF_6', A_264) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_264)))), inference(resolution, [status(thm)], [c_1440, c_1676])).
% 4.71/1.82  tff(c_1699, plain, (![B_9]: (r2_hidden('#skF_6', B_9) | ~r1_tarski('#skF_3', B_9))), inference(resolution, [status(thm)], [c_14, c_1694])).
% 4.71/1.82  tff(c_1704, plain, (![A_266, C_267, B_268]: (m1_subset_1(A_266, C_267) | ~m1_subset_1(B_268, k1_zfmisc_1(C_267)) | ~r2_hidden(A_266, B_268))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.71/1.82  tff(c_1727, plain, (![A_271, B_272, A_273]: (m1_subset_1(A_271, B_272) | ~r2_hidden(A_271, A_273) | ~r1_tarski(A_273, B_272))), inference(resolution, [status(thm)], [c_14, c_1704])).
% 4.71/1.82  tff(c_1756, plain, (![B_276, B_277]: (m1_subset_1('#skF_6', B_276) | ~r1_tarski(B_277, B_276) | ~r1_tarski('#skF_3', B_277))), inference(resolution, [status(thm)], [c_1699, c_1727])).
% 4.71/1.82  tff(c_1768, plain, (![A_3]: (m1_subset_1('#skF_6', A_3) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1756])).
% 4.71/1.82  tff(c_1786, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1768])).
% 4.71/1.82  tff(c_2177, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_1786])).
% 4.71/1.82  tff(c_2190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2177])).
% 4.71/1.82  tff(c_2192, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2172])).
% 4.71/1.82  tff(c_2191, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_2172])).
% 4.71/1.82  tff(c_2305, plain, (![D_340, B_341]: (k1_funct_1(k2_funct_1(D_340), k1_funct_1(D_340, '#skF_6'))='#skF_6' | k1_xboole_0=B_341 | ~v2_funct_1(D_340) | ~m1_subset_1(D_340, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_341))) | ~v1_funct_2(D_340, '#skF_3', B_341) | ~v1_funct_1(D_340))), inference(resolution, [status(thm)], [c_1440, c_2078])).
% 4.71/1.82  tff(c_2322, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_2305])).
% 4.71/1.82  tff(c_2330, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1437, c_2191, c_2322])).
% 4.71/1.82  tff(c_2332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2192, c_1436, c_2330])).
% 4.71/1.82  tff(c_2334, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1768])).
% 4.71/1.82  tff(c_1459, plain, (![B_224, A_225]: (B_224=A_225 | ~r1_tarski(B_224, A_225) | ~r1_tarski(A_225, B_224))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.71/1.82  tff(c_1471, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1459])).
% 4.71/1.82  tff(c_2378, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2334, c_1471])).
% 4.71/1.82  tff(c_2392, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2378, c_8])).
% 4.71/1.82  tff(c_2416, plain, (![B_9]: (r2_hidden('#skF_6', B_9))), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_1699])).
% 4.71/1.82  tff(c_1683, plain, (![A_262]: (r2_hidden('#skF_5', A_262) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_262)))), inference(resolution, [status(thm)], [c_1442, c_1676])).
% 4.71/1.82  tff(c_1688, plain, (![B_9]: (r2_hidden('#skF_5', B_9) | ~r1_tarski('#skF_3', B_9))), inference(resolution, [status(thm)], [c_14, c_1683])).
% 4.71/1.82  tff(c_2418, plain, (![B_9]: (r2_hidden('#skF_5', B_9))), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_1688])).
% 4.71/1.82  tff(c_1485, plain, (![B_227, A_228]: (v1_relat_1(B_227) | ~m1_subset_1(B_227, k1_zfmisc_1(A_228)) | ~v1_relat_1(A_228))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.71/1.82  tff(c_1491, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_1485])).
% 4.71/1.82  tff(c_1495, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1491])).
% 4.71/1.82  tff(c_2464, plain, (![C_350, B_351, A_352]: (C_350=B_351 | k1_funct_1(A_352, C_350)!=k1_funct_1(A_352, B_351) | ~r2_hidden(C_350, k1_relat_1(A_352)) | ~r2_hidden(B_351, k1_relat_1(A_352)) | ~v2_funct_1(A_352) | ~v1_funct_1(A_352) | ~v1_relat_1(A_352))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.71/1.82  tff(c_2472, plain, (![C_350]: (C_350='#skF_5' | k1_funct_1('#skF_4', C_350)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_350, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1454, c_2464])).
% 4.71/1.82  tff(c_2476, plain, (![C_350]: (C_350='#skF_5' | k1_funct_1('#skF_4', C_350)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_350, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_46, c_1437, c_2472])).
% 4.71/1.82  tff(c_2527, plain, (![C_356]: (C_356='#skF_5' | k1_funct_1('#skF_4', C_356)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_356, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2476])).
% 4.71/1.82  tff(c_2531, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2416, c_2527])).
% 4.71/1.82  tff(c_2547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1436, c_2531])).
% 4.71/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.82  
% 4.71/1.82  Inference rules
% 4.71/1.82  ----------------------
% 4.71/1.82  #Ref     : 5
% 4.71/1.82  #Sup     : 505
% 4.71/1.82  #Fact    : 0
% 4.71/1.82  #Define  : 0
% 4.71/1.82  #Split   : 21
% 4.71/1.82  #Chain   : 0
% 4.71/1.82  #Close   : 0
% 4.71/1.82  
% 4.71/1.82  Ordering : KBO
% 4.71/1.82  
% 4.71/1.82  Simplification rules
% 4.71/1.82  ----------------------
% 4.71/1.82  #Subsume      : 86
% 4.71/1.82  #Demod        : 293
% 4.71/1.82  #Tautology    : 107
% 4.71/1.82  #SimpNegUnit  : 17
% 4.71/1.82  #BackRed      : 32
% 4.71/1.82  
% 4.71/1.82  #Partial instantiations: 0
% 4.71/1.82  #Strategies tried      : 1
% 4.71/1.82  
% 4.71/1.82  Timing (in seconds)
% 4.71/1.82  ----------------------
% 4.71/1.83  Preprocessing        : 0.32
% 4.71/1.83  Parsing              : 0.17
% 4.71/1.83  CNF conversion       : 0.02
% 4.71/1.83  Main loop            : 0.71
% 4.71/1.83  Inferencing          : 0.26
% 4.71/1.83  Reduction            : 0.22
% 4.71/1.83  Demodulation         : 0.15
% 4.71/1.83  BG Simplification    : 0.03
% 4.71/1.83  Subsumption          : 0.14
% 4.71/1.83  Abstraction          : 0.04
% 4.71/1.83  MUC search           : 0.00
% 4.71/1.83  Cooper               : 0.00
% 4.71/1.83  Total                : 1.07
% 4.71/1.83  Index Insertion      : 0.00
% 4.71/1.83  Index Deletion       : 0.00
% 4.71/1.83  Index Matching       : 0.00
% 4.71/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
