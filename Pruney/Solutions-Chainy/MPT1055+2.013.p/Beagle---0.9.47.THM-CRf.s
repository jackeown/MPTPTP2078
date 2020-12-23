%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:20 EST 2020

% Result     : Theorem 15.84s
% Output     : CNFRefutation 15.84s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 643 expanded)
%              Number of leaves         :   52 ( 245 expanded)
%              Depth                    :   17
%              Number of atoms          :  338 (1821 expanded)
%              Number of equality atoms :   49 ( 215 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_217,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_165,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_192,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_177,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_117,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_137,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(A_106,B_107)
      | ~ m1_subset_1(A_106,k1_zfmisc_1(B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_158,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_137])).

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_88,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_39198,plain,(
    ! [C_1386,A_1387,B_1388] :
      ( ~ v1_xboole_0(C_1386)
      | ~ v1_funct_2(C_1386,A_1387,B_1388)
      | ~ v1_funct_1(C_1386)
      | ~ m1_subset_1(C_1386,k1_zfmisc_1(k2_zfmisc_1(A_1387,B_1388)))
      | v1_xboole_0(B_1388)
      | v1_xboole_0(A_1387) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_39208,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_39198])).

tff(c_39223,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_39208])).

tff(c_39224,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_39223])).

tff(c_34,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36707,plain,(
    ! [B_1175,A_1176] :
      ( v1_relat_1(B_1175)
      | ~ m1_subset_1(B_1175,k1_zfmisc_1(A_1176))
      | ~ v1_relat_1(A_1176) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36713,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_36707])).

tff(c_36726,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36713])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38259,plain,(
    ! [A_1332,B_1333,C_1334,D_1335] :
      ( k7_relset_1(A_1332,B_1333,C_1334,D_1335) = k9_relat_1(C_1334,D_1335)
      | ~ m1_subset_1(C_1334,k1_zfmisc_1(k2_zfmisc_1(A_1332,B_1333))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_38273,plain,(
    ! [D_1335] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_1335) = k9_relat_1('#skF_3',D_1335) ),
    inference(resolution,[status(thm)],[c_86,c_38259])).

tff(c_37571,plain,(
    ! [A_1267,B_1268,C_1269] :
      ( k2_relset_1(A_1267,B_1268,C_1269) = k2_relat_1(C_1269)
      | ~ m1_subset_1(C_1269,k1_zfmisc_1(k2_zfmisc_1(A_1267,B_1268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_37590,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_37571])).

tff(c_38793,plain,(
    ! [A_1368,B_1369,C_1370] :
      ( k7_relset_1(A_1368,B_1369,C_1370,A_1368) = k2_relset_1(A_1368,B_1369,C_1370)
      | ~ m1_subset_1(C_1370,k1_zfmisc_1(k2_zfmisc_1(A_1368,B_1369))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38800,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_38793])).

tff(c_38811,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38273,c_37590,c_38800])).

tff(c_36,plain,(
    ! [C_24,A_22,B_23] :
      ( r1_tarski(k9_relat_1(C_24,A_22),k9_relat_1(C_24,B_23))
      | ~ r1_tarski(A_22,B_23)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38919,plain,(
    ! [B_23] :
      ( r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3',B_23))
      | ~ r1_tarski('#skF_1',B_23)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38811,c_36])).

tff(c_38930,plain,(
    ! [B_23] :
      ( r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3',B_23))
      | ~ r1_tarski('#skF_1',B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36726,c_38919])).

tff(c_38526,plain,(
    ! [A_1350,B_1351,C_1352,D_1353] :
      ( k8_relset_1(A_1350,B_1351,C_1352,D_1353) = k10_relat_1(C_1352,D_1353)
      | ~ m1_subset_1(C_1352,k1_zfmisc_1(k2_zfmisc_1(A_1350,B_1351))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_38540,plain,(
    ! [D_1353] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_1353) = k10_relat_1('#skF_3',D_1353) ),
    inference(resolution,[status(thm)],[c_86,c_38526])).

tff(c_37688,plain,(
    ! [A_1282,B_1283,C_1284] :
      ( k1_relset_1(A_1282,B_1283,C_1284) = k1_relat_1(C_1284)
      | ~ m1_subset_1(C_1284,k1_zfmisc_1(k2_zfmisc_1(A_1282,B_1283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_37707,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_37688])).

tff(c_39015,plain,(
    ! [A_1377,B_1378,C_1379] :
      ( k8_relset_1(A_1377,B_1378,C_1379,B_1378) = k1_relset_1(A_1377,B_1378,C_1379)
      | ~ m1_subset_1(C_1379,k1_zfmisc_1(k2_zfmisc_1(A_1377,B_1378))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_39022,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_39015])).

tff(c_39033,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38540,c_37707,c_39022])).

tff(c_40,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k9_relat_1(B_30,k10_relat_1(B_30,A_29)),A_29)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_39039,plain,
    ( r1_tarski(k9_relat_1('#skF_3',k1_relat_1('#skF_3')),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_39033,c_40])).

tff(c_39043,plain,(
    r1_tarski(k9_relat_1('#skF_3',k1_relat_1('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36726,c_90,c_39039])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_39145,plain,(
    ! [A_1385] :
      ( r1_tarski(A_1385,'#skF_2')
      | ~ r1_tarski(A_1385,k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_39043,c_10])).

tff(c_39182,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38930,c_39145])).

tff(c_39197,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_39182])).

tff(c_40710,plain,(
    ! [B_1441,A_1442,C_1443] :
      ( k8_relset_1(B_1441,A_1442,C_1443,k7_relset_1(B_1441,A_1442,C_1443,B_1441)) = k1_relset_1(B_1441,A_1442,C_1443)
      | ~ m1_subset_1(C_1443,k1_zfmisc_1(k2_zfmisc_1(B_1441,A_1442))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_40717,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_40710])).

tff(c_40728,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37707,c_38540,c_38811,c_38273,c_40717])).

tff(c_36954,plain,(
    ! [C_1206,B_1207,A_1208] :
      ( v5_relat_1(C_1206,B_1207)
      | ~ m1_subset_1(C_1206,k1_zfmisc_1(k2_zfmisc_1(A_1208,B_1207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36973,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_36954])).

tff(c_41003,plain,(
    ! [B_1452,C_1453,A_1454,D_1455] :
      ( k1_xboole_0 = B_1452
      | r1_tarski(C_1453,k8_relset_1(A_1454,B_1452,D_1455,k7_relset_1(A_1454,B_1452,D_1455,C_1453)))
      | ~ r1_tarski(C_1453,A_1454)
      | ~ m1_subset_1(D_1455,k1_zfmisc_1(k2_zfmisc_1(A_1454,B_1452)))
      | ~ v1_funct_2(D_1455,A_1454,B_1452)
      | ~ v1_funct_1(D_1455) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_41040,plain,(
    ! [C_1453] :
      ( k1_xboole_0 = '#skF_2'
      | r1_tarski(C_1453,k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3',C_1453)))
      | ~ r1_tarski(C_1453,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38540,c_41003])).

tff(c_41058,plain,(
    ! [C_1453] :
      ( k1_xboole_0 = '#skF_2'
      | r1_tarski(C_1453,k10_relat_1('#skF_3',k9_relat_1('#skF_3',C_1453)))
      | ~ r1_tarski(C_1453,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_38273,c_41040])).

tff(c_41136,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_41058])).

tff(c_37037,plain,(
    ! [B_1221,A_1222] :
      ( r1_tarski(k2_relat_1(B_1221),A_1222)
      | ~ v5_relat_1(B_1221,A_1222)
      | ~ v1_relat_1(B_1221) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36846,plain,(
    ! [A_1197,C_1198,B_1199] :
      ( r1_tarski(A_1197,C_1198)
      | ~ r1_tarski(B_1199,C_1198)
      | ~ r1_tarski(A_1197,B_1199) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36864,plain,(
    ! [A_1197,A_6] :
      ( r1_tarski(A_1197,A_6)
      | ~ r1_tarski(A_1197,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_36846])).

tff(c_37079,plain,(
    ! [B_1221,A_6] :
      ( r1_tarski(k2_relat_1(B_1221),A_6)
      | ~ v5_relat_1(B_1221,k1_xboole_0)
      | ~ v1_relat_1(B_1221) ) ),
    inference(resolution,[status(thm)],[c_37037,c_36864])).

tff(c_40558,plain,(
    ! [B_1437,A_1438,C_1439] :
      ( k7_relset_1(B_1437,A_1438,C_1439,k8_relset_1(B_1437,A_1438,C_1439,A_1438)) = k2_relset_1(B_1437,A_1438,C_1439)
      | ~ m1_subset_1(C_1439,k1_zfmisc_1(k2_zfmisc_1(B_1437,A_1438))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_40565,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_40558])).

tff(c_40576,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37590,c_38273,c_39033,c_38540,c_40565])).

tff(c_42,plain,(
    ! [A_31,C_33,B_32] :
      ( r1_tarski(A_31,k10_relat_1(C_33,B_32))
      | ~ r1_tarski(k9_relat_1(C_33,A_31),B_32)
      | ~ r1_tarski(A_31,k1_relat_1(C_33))
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40590,plain,(
    ! [B_32] :
      ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',B_32))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_32)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40576,c_42])).

tff(c_40955,plain,(
    ! [B_1451] :
      ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',B_1451))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_1451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36726,c_90,c_8,c_40590])).

tff(c_37415,plain,(
    ! [B_1256,A_1257] :
      ( r1_tarski(k9_relat_1(B_1256,k10_relat_1(B_1256,A_1257)),A_1257)
      | ~ v1_funct_1(B_1256)
      | ~ v1_relat_1(B_1256) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36670,plain,(
    ! [B_1172,A_1173] :
      ( B_1172 = A_1173
      | ~ r1_tarski(B_1172,A_1173)
      | ~ r1_tarski(A_1173,B_1172) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36691,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_36670])).

tff(c_37476,plain,(
    ! [B_1256] :
      ( k9_relat_1(B_1256,k10_relat_1(B_1256,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_1256)
      | ~ v1_relat_1(B_1256) ) ),
    inference(resolution,[status(thm)],[c_37415,c_36691])).

tff(c_40620,plain,(
    ! [B_23] :
      ( r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3',B_23))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_23)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40576,c_36])).

tff(c_40875,plain,(
    ! [B_1449] :
      ( r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3',B_1449))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_1449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36726,c_40620])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( v5_relat_1(B_19,A_18)
      | ~ r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40892,plain,(
    ! [B_1449] :
      ( v5_relat_1('#skF_3',k9_relat_1('#skF_3',B_1449))
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_1449) ) ),
    inference(resolution,[status(thm)],[c_40875,c_30])).

tff(c_40925,plain,(
    ! [B_1450] :
      ( v5_relat_1('#skF_3',k9_relat_1('#skF_3',B_1450))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_1450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36726,c_40892])).

tff(c_40941,plain,
    ( v5_relat_1('#skF_3',k1_xboole_0)
    | ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k1_xboole_0))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37476,c_40925])).

tff(c_40952,plain,
    ( v5_relat_1('#skF_3',k1_xboole_0)
    | ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36726,c_90,c_40941])).

tff(c_40953,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_40952])).

tff(c_40976,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40955,c_40953])).

tff(c_40988,plain,
    ( ~ v5_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_37079,c_40976])).

tff(c_40994,plain,(
    ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36726,c_40988])).

tff(c_41138,plain,(
    ~ v5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41136,c_40994])).

tff(c_41200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36973,c_41138])).

tff(c_41203,plain,(
    ! [C_1459] :
      ( r1_tarski(C_1459,k10_relat_1('#skF_3',k9_relat_1('#skF_3',C_1459)))
      | ~ r1_tarski(C_1459,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_41058])).

tff(c_41235,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38811,c_41203])).

tff(c_41253,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_40728,c_41235])).

tff(c_41255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39197,c_41253])).

tff(c_41256,plain,(
    v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_40952])).

tff(c_37084,plain,(
    ! [B_1221] :
      ( k2_relat_1(B_1221) = k1_xboole_0
      | ~ v5_relat_1(B_1221,k1_xboole_0)
      | ~ v1_relat_1(B_1221) ) ),
    inference(resolution,[status(thm)],[c_37037,c_36691])).

tff(c_41264,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_41256,c_37084])).

tff(c_41273,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36726,c_41264])).

tff(c_16,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38629,plain,(
    ! [B_1360,A_1361] :
      ( m1_subset_1(B_1360,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1360),A_1361)))
      | ~ r1_tarski(k2_relat_1(B_1360),A_1361)
      | ~ v1_funct_1(B_1360)
      | ~ v1_relat_1(B_1360) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_41640,plain,(
    ! [B_1465] :
      ( m1_subset_1(B_1465,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_1465),k1_xboole_0)
      | ~ v1_funct_1(B_1465)
      | ~ v1_relat_1(B_1465) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_38629])).

tff(c_41643,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_41273,c_41640])).

tff(c_41656,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36726,c_90,c_8,c_41643])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_37167,plain,(
    ! [C_1228,B_1229,A_1230] :
      ( v1_xboole_0(C_1228)
      | ~ m1_subset_1(C_1228,k1_zfmisc_1(k2_zfmisc_1(B_1229,A_1230)))
      | ~ v1_xboole_0(A_1230) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_37184,plain,(
    ! [C_1228] :
      ( v1_xboole_0(C_1228)
      | ~ m1_subset_1(C_1228,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_37167])).

tff(c_37190,plain,(
    ! [C_1228] :
      ( v1_xboole_0(C_1228)
      | ~ m1_subset_1(C_1228,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_37184])).

tff(c_41673,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_41656,c_37190])).

tff(c_41694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39224,c_41673])).

tff(c_41696,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_39182])).

tff(c_41736,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_41696,c_10])).

tff(c_171,plain,(
    ! [B_110,A_111] :
      ( v1_relat_1(B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_111))
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_177,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_171])).

tff(c_190,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_177])).

tff(c_1595,plain,(
    ! [A_264,B_265,C_266,D_267] :
      ( k8_relset_1(A_264,B_265,C_266,D_267) = k10_relat_1(C_266,D_267)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1609,plain,(
    ! [D_267] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_267) = k10_relat_1('#skF_3',D_267) ),
    inference(resolution,[status(thm)],[c_86,c_1595])).

tff(c_102,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_159,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_1614,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1609,c_159])).

tff(c_751,plain,(
    ! [B_182,A_183] :
      ( r1_tarski(k9_relat_1(B_182,k10_relat_1(B_182,A_183)),A_183)
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_12007,plain,(
    ! [A_646,A_647,B_648] :
      ( r1_tarski(A_646,A_647)
      | ~ r1_tarski(A_646,k9_relat_1(B_648,k10_relat_1(B_648,A_647)))
      | ~ v1_funct_1(B_648)
      | ~ v1_relat_1(B_648) ) ),
    inference(resolution,[status(thm)],[c_751,c_10])).

tff(c_36130,plain,(
    ! [C_1169,A_1170,A_1171] :
      ( r1_tarski(k9_relat_1(C_1169,A_1170),A_1171)
      | ~ v1_funct_1(C_1169)
      | ~ r1_tarski(A_1170,k10_relat_1(C_1169,A_1171))
      | ~ v1_relat_1(C_1169) ) ),
    inference(resolution,[status(thm)],[c_36,c_12007])).

tff(c_1493,plain,(
    ! [A_252,B_253,C_254,D_255] :
      ( k7_relset_1(A_252,B_253,C_254,D_255) = k9_relat_1(C_254,D_255)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1507,plain,(
    ! [D_255] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_255) = k9_relat_1('#skF_3',D_255) ),
    inference(resolution,[status(thm)],[c_86,c_1493])).

tff(c_96,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_220,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_96])).

tff(c_1509,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_220])).

tff(c_36457,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36130,c_1509])).

tff(c_36665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_1614,c_90,c_36457])).

tff(c_36667,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_38542,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38540,c_36667])).

tff(c_36666,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_38279,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38273,c_36666])).

tff(c_41951,plain,(
    ! [A_1475,C_1476,B_1477] :
      ( r1_tarski(A_1475,k10_relat_1(C_1476,B_1477))
      | ~ r1_tarski(k9_relat_1(C_1476,A_1475),B_1477)
      | ~ r1_tarski(A_1475,k1_relat_1(C_1476))
      | ~ v1_funct_1(C_1476)
      | ~ v1_relat_1(C_1476) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_41994,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38279,c_41951])).

tff(c_42053,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36726,c_90,c_41994])).

tff(c_42054,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38542,c_42053])).

tff(c_42067,plain,(
    ~ r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_41736,c_42054])).

tff(c_42071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_42067])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:49:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.84/7.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.84/7.48  
% 15.84/7.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.84/7.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.84/7.49  
% 15.84/7.49  %Foreground sorts:
% 15.84/7.49  
% 15.84/7.49  
% 15.84/7.49  %Background operators:
% 15.84/7.49  
% 15.84/7.49  
% 15.84/7.49  %Foreground operators:
% 15.84/7.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 15.84/7.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.84/7.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.84/7.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.84/7.49  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 15.84/7.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.84/7.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.84/7.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.84/7.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 15.84/7.49  tff('#skF_5', type, '#skF_5': $i).
% 15.84/7.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.84/7.49  tff('#skF_2', type, '#skF_2': $i).
% 15.84/7.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 15.84/7.49  tff('#skF_3', type, '#skF_3': $i).
% 15.84/7.49  tff('#skF_1', type, '#skF_1': $i).
% 15.84/7.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.84/7.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.84/7.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.84/7.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.84/7.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 15.84/7.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.84/7.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.84/7.49  tff('#skF_4', type, '#skF_4': $i).
% 15.84/7.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.84/7.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.84/7.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.84/7.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.84/7.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.84/7.49  
% 15.84/7.51  tff(f_217, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 15.84/7.51  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 15.84/7.51  tff(f_165, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 15.84/7.51  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.84/7.51  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 15.84/7.51  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.84/7.51  tff(f_129, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 15.84/7.51  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 15.84/7.51  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 15.84/7.51  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 15.84/7.51  tff(f_133, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 15.84/7.51  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.84/7.51  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 15.84/7.51  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 15.84/7.51  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 15.84/7.51  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 15.84/7.51  tff(f_192, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_2)).
% 15.84/7.51  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 15.84/7.51  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 15.84/7.51  tff(f_104, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 15.84/7.51  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.84/7.51  tff(f_177, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 15.84/7.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 15.84/7.51  tff(f_117, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 15.84/7.51  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.84/7.51  tff(c_137, plain, (![A_106, B_107]: (r1_tarski(A_106, B_107) | ~m1_subset_1(A_106, k1_zfmisc_1(B_107)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.84/7.51  tff(c_158, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_137])).
% 15.84/7.51  tff(c_94, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.84/7.51  tff(c_92, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.84/7.51  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.84/7.51  tff(c_88, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.84/7.51  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.84/7.51  tff(c_39198, plain, (![C_1386, A_1387, B_1388]: (~v1_xboole_0(C_1386) | ~v1_funct_2(C_1386, A_1387, B_1388) | ~v1_funct_1(C_1386) | ~m1_subset_1(C_1386, k1_zfmisc_1(k2_zfmisc_1(A_1387, B_1388))) | v1_xboole_0(B_1388) | v1_xboole_0(A_1387))), inference(cnfTransformation, [status(thm)], [f_165])).
% 15.84/7.51  tff(c_39208, plain, (~v1_xboole_0('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_86, c_39198])).
% 15.84/7.51  tff(c_39223, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_39208])).
% 15.84/7.51  tff(c_39224, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_39223])).
% 15.84/7.51  tff(c_34, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.84/7.51  tff(c_36707, plain, (![B_1175, A_1176]: (v1_relat_1(B_1175) | ~m1_subset_1(B_1175, k1_zfmisc_1(A_1176)) | ~v1_relat_1(A_1176))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.84/7.51  tff(c_36713, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_36707])).
% 15.84/7.51  tff(c_36726, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36713])).
% 15.84/7.51  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.84/7.51  tff(c_38259, plain, (![A_1332, B_1333, C_1334, D_1335]: (k7_relset_1(A_1332, B_1333, C_1334, D_1335)=k9_relat_1(C_1334, D_1335) | ~m1_subset_1(C_1334, k1_zfmisc_1(k2_zfmisc_1(A_1332, B_1333))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 15.84/7.51  tff(c_38273, plain, (![D_1335]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_1335)=k9_relat_1('#skF_3', D_1335))), inference(resolution, [status(thm)], [c_86, c_38259])).
% 15.84/7.51  tff(c_37571, plain, (![A_1267, B_1268, C_1269]: (k2_relset_1(A_1267, B_1268, C_1269)=k2_relat_1(C_1269) | ~m1_subset_1(C_1269, k1_zfmisc_1(k2_zfmisc_1(A_1267, B_1268))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.84/7.51  tff(c_37590, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_37571])).
% 15.84/7.51  tff(c_38793, plain, (![A_1368, B_1369, C_1370]: (k7_relset_1(A_1368, B_1369, C_1370, A_1368)=k2_relset_1(A_1368, B_1369, C_1370) | ~m1_subset_1(C_1370, k1_zfmisc_1(k2_zfmisc_1(A_1368, B_1369))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 15.84/7.51  tff(c_38800, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_86, c_38793])).
% 15.84/7.51  tff(c_38811, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38273, c_37590, c_38800])).
% 15.84/7.51  tff(c_36, plain, (![C_24, A_22, B_23]: (r1_tarski(k9_relat_1(C_24, A_22), k9_relat_1(C_24, B_23)) | ~r1_tarski(A_22, B_23) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.84/7.51  tff(c_38919, plain, (![B_23]: (r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', B_23)) | ~r1_tarski('#skF_1', B_23) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_38811, c_36])).
% 15.84/7.51  tff(c_38930, plain, (![B_23]: (r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', B_23)) | ~r1_tarski('#skF_1', B_23))), inference(demodulation, [status(thm), theory('equality')], [c_36726, c_38919])).
% 15.84/7.51  tff(c_38526, plain, (![A_1350, B_1351, C_1352, D_1353]: (k8_relset_1(A_1350, B_1351, C_1352, D_1353)=k10_relat_1(C_1352, D_1353) | ~m1_subset_1(C_1352, k1_zfmisc_1(k2_zfmisc_1(A_1350, B_1351))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 15.84/7.51  tff(c_38540, plain, (![D_1353]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_1353)=k10_relat_1('#skF_3', D_1353))), inference(resolution, [status(thm)], [c_86, c_38526])).
% 15.84/7.51  tff(c_37688, plain, (![A_1282, B_1283, C_1284]: (k1_relset_1(A_1282, B_1283, C_1284)=k1_relat_1(C_1284) | ~m1_subset_1(C_1284, k1_zfmisc_1(k2_zfmisc_1(A_1282, B_1283))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 15.84/7.51  tff(c_37707, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_37688])).
% 15.84/7.51  tff(c_39015, plain, (![A_1377, B_1378, C_1379]: (k8_relset_1(A_1377, B_1378, C_1379, B_1378)=k1_relset_1(A_1377, B_1378, C_1379) | ~m1_subset_1(C_1379, k1_zfmisc_1(k2_zfmisc_1(A_1377, B_1378))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 15.84/7.51  tff(c_39022, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_86, c_39015])).
% 15.84/7.51  tff(c_39033, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38540, c_37707, c_39022])).
% 15.84/7.51  tff(c_40, plain, (![B_30, A_29]: (r1_tarski(k9_relat_1(B_30, k10_relat_1(B_30, A_29)), A_29) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.84/7.51  tff(c_39039, plain, (r1_tarski(k9_relat_1('#skF_3', k1_relat_1('#skF_3')), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_39033, c_40])).
% 15.84/7.51  tff(c_39043, plain, (r1_tarski(k9_relat_1('#skF_3', k1_relat_1('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36726, c_90, c_39039])).
% 15.84/7.51  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.84/7.51  tff(c_39145, plain, (![A_1385]: (r1_tarski(A_1385, '#skF_2') | ~r1_tarski(A_1385, k9_relat_1('#skF_3', k1_relat_1('#skF_3'))))), inference(resolution, [status(thm)], [c_39043, c_10])).
% 15.84/7.51  tff(c_39182, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_38930, c_39145])).
% 15.84/7.51  tff(c_39197, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_39182])).
% 15.84/7.51  tff(c_40710, plain, (![B_1441, A_1442, C_1443]: (k8_relset_1(B_1441, A_1442, C_1443, k7_relset_1(B_1441, A_1442, C_1443, B_1441))=k1_relset_1(B_1441, A_1442, C_1443) | ~m1_subset_1(C_1443, k1_zfmisc_1(k2_zfmisc_1(B_1441, A_1442))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 15.84/7.51  tff(c_40717, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_86, c_40710])).
% 15.84/7.51  tff(c_40728, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37707, c_38540, c_38811, c_38273, c_40717])).
% 15.84/7.51  tff(c_36954, plain, (![C_1206, B_1207, A_1208]: (v5_relat_1(C_1206, B_1207) | ~m1_subset_1(C_1206, k1_zfmisc_1(k2_zfmisc_1(A_1208, B_1207))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.84/7.51  tff(c_36973, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_86, c_36954])).
% 15.84/7.51  tff(c_41003, plain, (![B_1452, C_1453, A_1454, D_1455]: (k1_xboole_0=B_1452 | r1_tarski(C_1453, k8_relset_1(A_1454, B_1452, D_1455, k7_relset_1(A_1454, B_1452, D_1455, C_1453))) | ~r1_tarski(C_1453, A_1454) | ~m1_subset_1(D_1455, k1_zfmisc_1(k2_zfmisc_1(A_1454, B_1452))) | ~v1_funct_2(D_1455, A_1454, B_1452) | ~v1_funct_1(D_1455))), inference(cnfTransformation, [status(thm)], [f_192])).
% 15.84/7.51  tff(c_41040, plain, (![C_1453]: (k1_xboole_0='#skF_2' | r1_tarski(C_1453, k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', C_1453))) | ~r1_tarski(C_1453, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_38540, c_41003])).
% 15.84/7.51  tff(c_41058, plain, (![C_1453]: (k1_xboole_0='#skF_2' | r1_tarski(C_1453, k10_relat_1('#skF_3', k9_relat_1('#skF_3', C_1453))) | ~r1_tarski(C_1453, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_38273, c_41040])).
% 15.84/7.51  tff(c_41136, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_41058])).
% 15.84/7.51  tff(c_37037, plain, (![B_1221, A_1222]: (r1_tarski(k2_relat_1(B_1221), A_1222) | ~v5_relat_1(B_1221, A_1222) | ~v1_relat_1(B_1221))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.84/7.51  tff(c_12, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.84/7.51  tff(c_36846, plain, (![A_1197, C_1198, B_1199]: (r1_tarski(A_1197, C_1198) | ~r1_tarski(B_1199, C_1198) | ~r1_tarski(A_1197, B_1199))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.84/7.51  tff(c_36864, plain, (![A_1197, A_6]: (r1_tarski(A_1197, A_6) | ~r1_tarski(A_1197, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_36846])).
% 15.84/7.51  tff(c_37079, plain, (![B_1221, A_6]: (r1_tarski(k2_relat_1(B_1221), A_6) | ~v5_relat_1(B_1221, k1_xboole_0) | ~v1_relat_1(B_1221))), inference(resolution, [status(thm)], [c_37037, c_36864])).
% 15.84/7.51  tff(c_40558, plain, (![B_1437, A_1438, C_1439]: (k7_relset_1(B_1437, A_1438, C_1439, k8_relset_1(B_1437, A_1438, C_1439, A_1438))=k2_relset_1(B_1437, A_1438, C_1439) | ~m1_subset_1(C_1439, k1_zfmisc_1(k2_zfmisc_1(B_1437, A_1438))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 15.84/7.51  tff(c_40565, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_86, c_40558])).
% 15.84/7.51  tff(c_40576, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37590, c_38273, c_39033, c_38540, c_40565])).
% 15.84/7.51  tff(c_42, plain, (![A_31, C_33, B_32]: (r1_tarski(A_31, k10_relat_1(C_33, B_32)) | ~r1_tarski(k9_relat_1(C_33, A_31), B_32) | ~r1_tarski(A_31, k1_relat_1(C_33)) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.84/7.51  tff(c_40590, plain, (![B_32]: (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', B_32)) | ~r1_tarski(k2_relat_1('#skF_3'), B_32) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40576, c_42])).
% 15.84/7.51  tff(c_40955, plain, (![B_1451]: (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', B_1451)) | ~r1_tarski(k2_relat_1('#skF_3'), B_1451))), inference(demodulation, [status(thm), theory('equality')], [c_36726, c_90, c_8, c_40590])).
% 15.84/7.51  tff(c_37415, plain, (![B_1256, A_1257]: (r1_tarski(k9_relat_1(B_1256, k10_relat_1(B_1256, A_1257)), A_1257) | ~v1_funct_1(B_1256) | ~v1_relat_1(B_1256))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.84/7.51  tff(c_36670, plain, (![B_1172, A_1173]: (B_1172=A_1173 | ~r1_tarski(B_1172, A_1173) | ~r1_tarski(A_1173, B_1172))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.84/7.51  tff(c_36691, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_36670])).
% 15.84/7.51  tff(c_37476, plain, (![B_1256]: (k9_relat_1(B_1256, k10_relat_1(B_1256, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_1256) | ~v1_relat_1(B_1256))), inference(resolution, [status(thm)], [c_37415, c_36691])).
% 15.84/7.51  tff(c_40620, plain, (![B_23]: (r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', B_23)) | ~r1_tarski(k1_relat_1('#skF_3'), B_23) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40576, c_36])).
% 15.84/7.51  tff(c_40875, plain, (![B_1449]: (r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', B_1449)) | ~r1_tarski(k1_relat_1('#skF_3'), B_1449))), inference(demodulation, [status(thm), theory('equality')], [c_36726, c_40620])).
% 15.84/7.51  tff(c_30, plain, (![B_19, A_18]: (v5_relat_1(B_19, A_18) | ~r1_tarski(k2_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.84/7.51  tff(c_40892, plain, (![B_1449]: (v5_relat_1('#skF_3', k9_relat_1('#skF_3', B_1449)) | ~v1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), B_1449))), inference(resolution, [status(thm)], [c_40875, c_30])).
% 15.84/7.51  tff(c_40925, plain, (![B_1450]: (v5_relat_1('#skF_3', k9_relat_1('#skF_3', B_1450)) | ~r1_tarski(k1_relat_1('#skF_3'), B_1450))), inference(demodulation, [status(thm), theory('equality')], [c_36726, c_40892])).
% 15.84/7.51  tff(c_40941, plain, (v5_relat_1('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k1_xboole_0)) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37476, c_40925])).
% 15.84/7.51  tff(c_40952, plain, (v5_relat_1('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36726, c_90, c_40941])).
% 15.84/7.51  tff(c_40953, plain, (~r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_40952])).
% 15.84/7.51  tff(c_40976, plain, (~r1_tarski(k2_relat_1('#skF_3'), k1_xboole_0)), inference(resolution, [status(thm)], [c_40955, c_40953])).
% 15.84/7.51  tff(c_40988, plain, (~v5_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_37079, c_40976])).
% 15.84/7.51  tff(c_40994, plain, (~v5_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36726, c_40988])).
% 15.84/7.51  tff(c_41138, plain, (~v5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_41136, c_40994])).
% 15.84/7.51  tff(c_41200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36973, c_41138])).
% 15.84/7.51  tff(c_41203, plain, (![C_1459]: (r1_tarski(C_1459, k10_relat_1('#skF_3', k9_relat_1('#skF_3', C_1459))) | ~r1_tarski(C_1459, '#skF_1'))), inference(splitRight, [status(thm)], [c_41058])).
% 15.84/7.51  tff(c_41235, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38811, c_41203])).
% 15.84/7.51  tff(c_41253, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_40728, c_41235])).
% 15.84/7.51  tff(c_41255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39197, c_41253])).
% 15.84/7.51  tff(c_41256, plain, (v5_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_40952])).
% 15.84/7.51  tff(c_37084, plain, (![B_1221]: (k2_relat_1(B_1221)=k1_xboole_0 | ~v5_relat_1(B_1221, k1_xboole_0) | ~v1_relat_1(B_1221))), inference(resolution, [status(thm)], [c_37037, c_36691])).
% 15.84/7.51  tff(c_41264, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_41256, c_37084])).
% 15.84/7.51  tff(c_41273, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36726, c_41264])).
% 15.84/7.51  tff(c_16, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.84/7.51  tff(c_38629, plain, (![B_1360, A_1361]: (m1_subset_1(B_1360, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1360), A_1361))) | ~r1_tarski(k2_relat_1(B_1360), A_1361) | ~v1_funct_1(B_1360) | ~v1_relat_1(B_1360))), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.84/7.51  tff(c_41640, plain, (![B_1465]: (m1_subset_1(B_1465, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_1465), k1_xboole_0) | ~v1_funct_1(B_1465) | ~v1_relat_1(B_1465))), inference(superposition, [status(thm), theory('equality')], [c_16, c_38629])).
% 15.84/7.51  tff(c_41643, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_41273, c_41640])).
% 15.84/7.51  tff(c_41656, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36726, c_90, c_8, c_41643])).
% 15.84/7.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 15.84/7.51  tff(c_37167, plain, (![C_1228, B_1229, A_1230]: (v1_xboole_0(C_1228) | ~m1_subset_1(C_1228, k1_zfmisc_1(k2_zfmisc_1(B_1229, A_1230))) | ~v1_xboole_0(A_1230))), inference(cnfTransformation, [status(thm)], [f_117])).
% 15.84/7.51  tff(c_37184, plain, (![C_1228]: (v1_xboole_0(C_1228) | ~m1_subset_1(C_1228, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_37167])).
% 15.84/7.51  tff(c_37190, plain, (![C_1228]: (v1_xboole_0(C_1228) | ~m1_subset_1(C_1228, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_37184])).
% 15.84/7.51  tff(c_41673, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_41656, c_37190])).
% 15.84/7.51  tff(c_41694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39224, c_41673])).
% 15.84/7.51  tff(c_41696, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_39182])).
% 15.84/7.51  tff(c_41736, plain, (![A_3]: (r1_tarski(A_3, k1_relat_1('#skF_3')) | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_41696, c_10])).
% 15.84/7.51  tff(c_171, plain, (![B_110, A_111]: (v1_relat_1(B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_111)) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.84/7.51  tff(c_177, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_171])).
% 15.84/7.51  tff(c_190, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_177])).
% 15.84/7.51  tff(c_1595, plain, (![A_264, B_265, C_266, D_267]: (k8_relset_1(A_264, B_265, C_266, D_267)=k10_relat_1(C_266, D_267) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 15.84/7.51  tff(c_1609, plain, (![D_267]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_267)=k10_relat_1('#skF_3', D_267))), inference(resolution, [status(thm)], [c_86, c_1595])).
% 15.84/7.51  tff(c_102, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.84/7.51  tff(c_159, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_102])).
% 15.84/7.51  tff(c_1614, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1609, c_159])).
% 15.84/7.51  tff(c_751, plain, (![B_182, A_183]: (r1_tarski(k9_relat_1(B_182, k10_relat_1(B_182, A_183)), A_183) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.84/7.51  tff(c_12007, plain, (![A_646, A_647, B_648]: (r1_tarski(A_646, A_647) | ~r1_tarski(A_646, k9_relat_1(B_648, k10_relat_1(B_648, A_647))) | ~v1_funct_1(B_648) | ~v1_relat_1(B_648))), inference(resolution, [status(thm)], [c_751, c_10])).
% 15.84/7.51  tff(c_36130, plain, (![C_1169, A_1170, A_1171]: (r1_tarski(k9_relat_1(C_1169, A_1170), A_1171) | ~v1_funct_1(C_1169) | ~r1_tarski(A_1170, k10_relat_1(C_1169, A_1171)) | ~v1_relat_1(C_1169))), inference(resolution, [status(thm)], [c_36, c_12007])).
% 15.84/7.51  tff(c_1493, plain, (![A_252, B_253, C_254, D_255]: (k7_relset_1(A_252, B_253, C_254, D_255)=k9_relat_1(C_254, D_255) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 15.84/7.51  tff(c_1507, plain, (![D_255]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_255)=k9_relat_1('#skF_3', D_255))), inference(resolution, [status(thm)], [c_86, c_1493])).
% 15.84/7.51  tff(c_96, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.84/7.51  tff(c_220, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_96])).
% 15.84/7.51  tff(c_1509, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_220])).
% 15.84/7.51  tff(c_36457, plain, (~v1_funct_1('#skF_3') | ~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36130, c_1509])).
% 15.84/7.51  tff(c_36665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_1614, c_90, c_36457])).
% 15.84/7.51  tff(c_36667, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_102])).
% 15.84/7.51  tff(c_38542, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38540, c_36667])).
% 15.84/7.51  tff(c_36666, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_102])).
% 15.84/7.51  tff(c_38279, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38273, c_36666])).
% 15.84/7.51  tff(c_41951, plain, (![A_1475, C_1476, B_1477]: (r1_tarski(A_1475, k10_relat_1(C_1476, B_1477)) | ~r1_tarski(k9_relat_1(C_1476, A_1475), B_1477) | ~r1_tarski(A_1475, k1_relat_1(C_1476)) | ~v1_funct_1(C_1476) | ~v1_relat_1(C_1476))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.84/7.51  tff(c_41994, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38279, c_41951])).
% 15.84/7.51  tff(c_42053, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36726, c_90, c_41994])).
% 15.84/7.51  tff(c_42054, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38542, c_42053])).
% 15.84/7.51  tff(c_42067, plain, (~r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_41736, c_42054])).
% 15.84/7.51  tff(c_42071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_42067])).
% 15.84/7.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.84/7.51  
% 15.84/7.51  Inference rules
% 15.84/7.51  ----------------------
% 15.84/7.51  #Ref     : 0
% 15.84/7.51  #Sup     : 8996
% 15.84/7.51  #Fact    : 0
% 15.84/7.51  #Define  : 0
% 15.84/7.51  #Split   : 92
% 15.84/7.51  #Chain   : 0
% 15.84/7.51  #Close   : 0
% 15.84/7.51  
% 15.84/7.51  Ordering : KBO
% 15.84/7.51  
% 15.84/7.51  Simplification rules
% 15.84/7.51  ----------------------
% 15.84/7.51  #Subsume      : 3880
% 15.84/7.51  #Demod        : 6955
% 15.84/7.51  #Tautology    : 1501
% 15.84/7.51  #SimpNegUnit  : 248
% 15.84/7.51  #BackRed      : 406
% 15.84/7.51  
% 15.84/7.51  #Partial instantiations: 0
% 15.84/7.51  #Strategies tried      : 1
% 15.84/7.51  
% 15.84/7.51  Timing (in seconds)
% 15.84/7.51  ----------------------
% 15.84/7.51  Preprocessing        : 0.39
% 15.84/7.51  Parsing              : 0.21
% 15.84/7.51  CNF conversion       : 0.03
% 15.84/7.51  Main loop            : 6.34
% 15.84/7.51  Inferencing          : 1.40
% 15.84/7.52  Reduction            : 2.28
% 15.84/7.52  Demodulation         : 1.59
% 15.84/7.52  BG Simplification    : 0.12
% 15.84/7.52  Subsumption          : 2.11
% 15.84/7.52  Abstraction          : 0.19
% 15.84/7.52  MUC search           : 0.00
% 15.84/7.52  Cooper               : 0.00
% 15.84/7.52  Total                : 6.78
% 15.84/7.52  Index Insertion      : 0.00
% 15.84/7.52  Index Deletion       : 0.00
% 15.84/7.52  Index Matching       : 0.00
% 15.84/7.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
