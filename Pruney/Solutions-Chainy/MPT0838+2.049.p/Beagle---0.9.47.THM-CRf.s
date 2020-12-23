%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:16 EST 2020

% Result     : Theorem 25.04s
% Output     : CNFRefutation 25.04s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 527 expanded)
%              Number of leaves         :   49 ( 199 expanded)
%              Depth                    :   14
%              Number of atoms          :  226 (1102 expanded)
%              Number of equality atoms :   54 ( 266 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_88,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_55,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_52,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_72,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_92258,plain,(
    ! [A_1375,B_1376,C_1377] :
      ( k1_relset_1(A_1375,B_1376,C_1377) = k1_relat_1(C_1377)
      | ~ m1_subset_1(C_1377,k1_zfmisc_1(k2_zfmisc_1(A_1375,B_1376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_92274,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_92258])).

tff(c_70,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_92275,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92274,c_70])).

tff(c_92780,plain,(
    ! [A_1395,B_1396,C_1397] :
      ( k3_relset_1(A_1395,B_1396,C_1397) = k4_relat_1(C_1397)
      | ~ m1_subset_1(C_1397,k1_zfmisc_1(k2_zfmisc_1(A_1395,B_1396))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_92796,plain,(
    k3_relset_1('#skF_6','#skF_7','#skF_8') = k4_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_92780])).

tff(c_93234,plain,(
    ! [A_1420,B_1421,C_1422] :
      ( m1_subset_1(k3_relset_1(A_1420,B_1421,C_1422),k1_zfmisc_1(k2_zfmisc_1(B_1421,A_1420)))
      | ~ m1_subset_1(C_1422,k1_zfmisc_1(k2_zfmisc_1(A_1420,B_1421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_93258,plain,
    ( m1_subset_1(k4_relat_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_92796,c_93234])).

tff(c_93269,plain,(
    m1_subset_1(k4_relat_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_93258])).

tff(c_60,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_93292,plain,(
    k2_relset_1('#skF_7','#skF_6',k4_relat_1('#skF_8')) = k2_relat_1(k4_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_93269,c_60])).

tff(c_93906,plain,(
    ! [B_1443,A_1444,C_1445] :
      ( k2_relset_1(B_1443,A_1444,k3_relset_1(A_1444,B_1443,C_1445)) = k1_relset_1(A_1444,B_1443,C_1445)
      | ~ m1_subset_1(C_1445,k1_zfmisc_1(k2_zfmisc_1(A_1444,B_1443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_93926,plain,(
    k2_relset_1('#skF_7','#skF_6',k3_relset_1('#skF_6','#skF_7','#skF_8')) = k1_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_93906])).

tff(c_93938,plain,(
    k2_relat_1(k4_relat_1('#skF_8')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93292,c_92796,c_92274,c_93926])).

tff(c_46,plain,(
    ! [A_39] :
      ( v1_xboole_0(k2_relat_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_93958,plain,
    ( v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_xboole_0(k4_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93938,c_46])).

tff(c_93966,plain,(
    ~ v1_xboole_0(k4_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_93958])).

tff(c_48,plain,(
    ! [A_40,B_41] : v1_relat_1(k2_zfmisc_1(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    ! [B_36,A_34] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_93287,plain,
    ( v1_relat_1(k4_relat_1('#skF_8'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_93269,c_40])).

tff(c_93298,plain,(
    v1_relat_1(k4_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_93287])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_93293,plain,(
    k1_relset_1('#skF_7','#skF_6',k4_relat_1('#skF_8')) = k1_relat_1(k4_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_93269,c_58])).

tff(c_56501,plain,(
    ! [A_803,B_804,C_805] :
      ( k1_relset_1(A_803,B_804,C_805) = k1_relat_1(C_805)
      | ~ m1_subset_1(C_805,k1_zfmisc_1(k2_zfmisc_1(A_803,B_804))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_56517,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_56501])).

tff(c_56518,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56517,c_70])).

tff(c_56793,plain,(
    ! [A_816,B_817,C_818] :
      ( k3_relset_1(A_816,B_817,C_818) = k4_relat_1(C_818)
      | ~ m1_subset_1(C_818,k1_zfmisc_1(k2_zfmisc_1(A_816,B_817))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_56809,plain,(
    k3_relset_1('#skF_6','#skF_7','#skF_8') = k4_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_56793])).

tff(c_58022,plain,(
    ! [A_861,B_862,C_863] :
      ( m1_subset_1(k3_relset_1(A_861,B_862,C_863),k1_zfmisc_1(k2_zfmisc_1(B_862,A_861)))
      | ~ m1_subset_1(C_863,k1_zfmisc_1(k2_zfmisc_1(A_861,B_862))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_58046,plain,
    ( m1_subset_1(k4_relat_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_56809,c_58022])).

tff(c_58057,plain,(
    m1_subset_1(k4_relat_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_58046])).

tff(c_62,plain,(
    ! [A_55,B_56,C_57] :
      ( k3_relset_1(A_55,B_56,C_57) = k4_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_58079,plain,(
    k3_relset_1('#skF_7','#skF_6',k4_relat_1('#skF_8')) = k4_relat_1(k4_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_58057,c_62])).

tff(c_56,plain,(
    ! [A_46,B_47,C_48] :
      ( m1_subset_1(k3_relset_1(A_46,B_47,C_48),k1_zfmisc_1(k2_zfmisc_1(B_47,A_46)))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_58168,plain,
    ( m1_subset_1(k4_relat_1(k4_relat_1('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ m1_subset_1(k4_relat_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_58079,c_56])).

tff(c_58172,plain,(
    m1_subset_1(k4_relat_1(k4_relat_1('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58057,c_58168])).

tff(c_52,plain,(
    ! [C_45,B_44,A_43] :
      ( v5_relat_1(C_45,B_44)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_58207,plain,(
    v5_relat_1(k4_relat_1(k4_relat_1('#skF_8')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_58172,c_52])).

tff(c_58200,plain,
    ( v1_relat_1(k4_relat_1(k4_relat_1('#skF_8')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_58172,c_40])).

tff(c_58211,plain,(
    v1_relat_1(k4_relat_1(k4_relat_1('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_58200])).

tff(c_58080,plain,(
    k1_relset_1('#skF_7','#skF_6',k4_relat_1('#skF_8')) = k1_relat_1(k4_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_58057,c_58])).

tff(c_56399,plain,(
    ! [A_797,B_798,C_799] :
      ( k2_relset_1(A_797,B_798,C_799) = k2_relat_1(C_799)
      | ~ m1_subset_1(C_799,k1_zfmisc_1(k2_zfmisc_1(A_797,B_798))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_56415,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_56399])).

tff(c_58441,plain,(
    ! [B_885,A_886,C_887] :
      ( k1_relset_1(B_885,A_886,k3_relset_1(A_886,B_885,C_887)) = k2_relset_1(A_886,B_885,C_887)
      | ~ m1_subset_1(C_887,k1_zfmisc_1(k2_zfmisc_1(A_886,B_885))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58461,plain,(
    k1_relset_1('#skF_7','#skF_6',k3_relset_1('#skF_6','#skF_7','#skF_8')) = k2_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_58441])).

tff(c_58473,plain,(
    k1_relat_1(k4_relat_1('#skF_8')) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58080,c_56809,c_56415,c_58461])).

tff(c_58369,plain,(
    ! [B_881,A_882,C_883] :
      ( k2_relset_1(B_881,A_882,k3_relset_1(A_882,B_881,C_883)) = k1_relset_1(A_882,B_881,C_883)
      | ~ m1_subset_1(C_883,k1_zfmisc_1(k2_zfmisc_1(A_882,B_881))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58373,plain,(
    k2_relset_1('#skF_6','#skF_7',k3_relset_1('#skF_7','#skF_6',k4_relat_1('#skF_8'))) = k1_relset_1('#skF_7','#skF_6',k4_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_58057,c_58369])).

tff(c_58392,plain,(
    k2_relset_1('#skF_6','#skF_7',k4_relat_1(k4_relat_1('#skF_8'))) = k1_relat_1(k4_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58079,c_58080,c_58373])).

tff(c_58526,plain,(
    k2_relset_1('#skF_6','#skF_7',k4_relat_1(k4_relat_1('#skF_8'))) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58473,c_58392])).

tff(c_36,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58212,plain,(
    r1_tarski(k4_relat_1(k4_relat_1('#skF_8')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_58172,c_36])).

tff(c_38,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(A_32,k1_zfmisc_1(B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_59647,plain,(
    ! [A_932,B_933,A_934] :
      ( k2_relset_1(A_932,B_933,A_934) = k2_relat_1(A_934)
      | ~ r1_tarski(A_934,k2_zfmisc_1(A_932,B_933)) ) ),
    inference(resolution,[status(thm)],[c_38,c_56399])).

tff(c_59654,plain,(
    k2_relset_1('#skF_6','#skF_7',k4_relat_1(k4_relat_1('#skF_8'))) = k2_relat_1(k4_relat_1(k4_relat_1('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_58212,c_59647])).

tff(c_59675,plain,(
    k2_relat_1(k4_relat_1(k4_relat_1('#skF_8'))) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58526,c_59654])).

tff(c_44,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v5_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_59693,plain,(
    ! [A_37] :
      ( r1_tarski(k2_relat_1('#skF_8'),A_37)
      | ~ v5_relat_1(k4_relat_1(k4_relat_1('#skF_8')),A_37)
      | ~ v1_relat_1(k4_relat_1(k4_relat_1('#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59675,c_44])).

tff(c_61996,plain,(
    ! [A_970] :
      ( r1_tarski(k2_relat_1('#skF_8'),A_970)
      | ~ v5_relat_1(k4_relat_1(k4_relat_1('#skF_8')),A_970) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58211,c_59693])).

tff(c_62004,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_58207,c_61996])).

tff(c_58081,plain,(
    k2_relset_1('#skF_7','#skF_6',k4_relat_1('#skF_8')) = k2_relat_1(k4_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_58057,c_60])).

tff(c_58389,plain,(
    k2_relset_1('#skF_7','#skF_6',k3_relset_1('#skF_6','#skF_7','#skF_8')) = k1_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_58369])).

tff(c_58401,plain,(
    k2_relat_1(k4_relat_1('#skF_8')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58081,c_56809,c_56517,c_58389])).

tff(c_58418,plain,
    ( v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_xboole_0(k4_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58401,c_46])).

tff(c_58426,plain,(
    ~ v1_xboole_0(k4_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_58418])).

tff(c_58075,plain,
    ( v1_relat_1(k4_relat_1('#skF_8'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_58057,c_40])).

tff(c_58086,plain,(
    v1_relat_1(k4_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_58075])).

tff(c_50,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k1_relat_1(A_42))
      | ~ v1_relat_1(A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58478,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_8'))
    | ~ v1_relat_1(k4_relat_1('#skF_8'))
    | v1_xboole_0(k4_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58473,c_50])).

tff(c_58482,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_8'))
    | v1_xboole_0(k4_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58086,c_58478])).

tff(c_58483,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_58426,c_58482])).

tff(c_30,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_26] : k3_tarski(k1_zfmisc_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(A_30,B_31)
      | v1_xboole_0(B_31)
      | ~ m1_subset_1(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56011,plain,(
    ! [C_774,A_775,D_776] :
      ( r2_hidden(C_774,k3_tarski(A_775))
      | ~ r2_hidden(D_776,A_775)
      | ~ r2_hidden(C_774,D_776) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62596,plain,(
    ! [C_989,B_990,A_991] :
      ( r2_hidden(C_989,k3_tarski(B_990))
      | ~ r2_hidden(C_989,A_991)
      | v1_xboole_0(B_990)
      | ~ m1_subset_1(A_991,B_990) ) ),
    inference(resolution,[status(thm)],[c_34,c_56011])).

tff(c_87505,plain,(
    ! [A_1293,B_1294] :
      ( r2_hidden('#skF_1'(A_1293),k3_tarski(B_1294))
      | v1_xboole_0(B_1294)
      | ~ m1_subset_1(A_1293,B_1294)
      | v1_xboole_0(A_1293) ) ),
    inference(resolution,[status(thm)],[c_4,c_62596])).

tff(c_87661,plain,(
    ! [A_1293,A_26] :
      ( r2_hidden('#skF_1'(A_1293),A_26)
      | v1_xboole_0(k1_zfmisc_1(A_26))
      | ~ m1_subset_1(A_1293,k1_zfmisc_1(A_26))
      | v1_xboole_0(A_1293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_87505])).

tff(c_88081,plain,(
    ! [A_1301,A_1302] :
      ( r2_hidden('#skF_1'(A_1301),A_1302)
      | ~ m1_subset_1(A_1301,k1_zfmisc_1(A_1302))
      | v1_xboole_0(A_1301) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_87661])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91522,plain,(
    ! [A_1327,A_1328] :
      ( m1_subset_1('#skF_1'(A_1327),A_1328)
      | ~ m1_subset_1(A_1327,k1_zfmisc_1(A_1328))
      | v1_xboole_0(A_1327) ) ),
    inference(resolution,[status(thm)],[c_88081,c_32])).

tff(c_163,plain,(
    ! [D_91] :
      ( ~ r2_hidden(D_91,k2_relset_1('#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1(D_91,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_168,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_6','#skF_7','#skF_8')),'#skF_7')
    | v1_xboole_0(k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_4,c_163])).

tff(c_224,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_6','#skF_7','#skF_8')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_56418,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_8')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56415,c_224])).

tff(c_91593,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_91522,c_56418])).

tff(c_91675,plain,(
    ~ m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_58483,c_91593])).

tff(c_91822,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_91675])).

tff(c_91826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62004,c_91822])).

tff(c_91827,plain,(
    v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_58418])).

tff(c_91,plain,(
    ! [B_82,A_83] :
      ( ~ v1_xboole_0(B_82)
      | B_82 = A_83
      | ~ v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_97,plain,(
    ! [A_83] :
      ( k1_xboole_0 = A_83
      | ~ v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_91874,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91827,c_97])).

tff(c_91902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56518,c_91874])).

tff(c_91903,plain,(
    v1_xboole_0(k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_91917,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91903,c_97])).

tff(c_93981,plain,(
    ! [B_1448,A_1449,C_1450] :
      ( k1_relset_1(B_1448,A_1449,k3_relset_1(A_1449,B_1448,C_1450)) = k2_relset_1(A_1449,B_1448,C_1450)
      | ~ m1_subset_1(C_1450,k1_zfmisc_1(k2_zfmisc_1(A_1449,B_1448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_94001,plain,(
    k1_relset_1('#skF_7','#skF_6',k3_relset_1('#skF_6','#skF_7','#skF_8')) = k2_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_93981])).

tff(c_94013,plain,(
    k1_relat_1(k4_relat_1('#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93293,c_92796,c_91917,c_94001])).

tff(c_94018,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1('#skF_8'))
    | v1_xboole_0(k4_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94013,c_50])).

tff(c_94022,plain,(
    v1_xboole_0(k4_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93298,c_6,c_94018])).

tff(c_94024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93966,c_94022])).

tff(c_94025,plain,(
    v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_93958])).

tff(c_94057,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94025,c_97])).

tff(c_94077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92275,c_94057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:06:24 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.04/15.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.04/15.45  
% 25.04/15.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.04/15.45  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 25.04/15.45  
% 25.04/15.45  %Foreground sorts:
% 25.04/15.45  
% 25.04/15.45  
% 25.04/15.45  %Background operators:
% 25.04/15.45  
% 25.04/15.45  
% 25.04/15.45  %Foreground operators:
% 25.04/15.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 25.04/15.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.04/15.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.04/15.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 25.04/15.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.04/15.45  tff('#skF_7', type, '#skF_7': $i).
% 25.04/15.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 25.04/15.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.04/15.45  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 25.04/15.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 25.04/15.45  tff('#skF_6', type, '#skF_6': $i).
% 25.04/15.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 25.04/15.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 25.04/15.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 25.04/15.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.04/15.45  tff('#skF_8', type, '#skF_8': $i).
% 25.04/15.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.04/15.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 25.04/15.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 25.04/15.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 25.04/15.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.04/15.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 25.04/15.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 25.04/15.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 25.04/15.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 25.04/15.45  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 25.04/15.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 25.04/15.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.04/15.45  
% 25.04/15.47  tff(f_145, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 25.04/15.47  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 25.04/15.47  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 25.04/15.47  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 25.04/15.47  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 25.04/15.47  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 25.04/15.47  tff(f_86, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 25.04/15.47  tff(f_88, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 25.04/15.47  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 25.04/15.47  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 25.04/15.47  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 25.04/15.47  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 25.04/15.47  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 25.04/15.47  tff(f_96, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 25.04/15.47  tff(f_55, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 25.04/15.47  tff(f_52, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 25.04/15.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 25.04/15.47  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 25.04/15.47  tff(f_50, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 25.04/15.47  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 25.04/15.47  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 25.04/15.47  tff(c_72, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 25.04/15.47  tff(c_92258, plain, (![A_1375, B_1376, C_1377]: (k1_relset_1(A_1375, B_1376, C_1377)=k1_relat_1(C_1377) | ~m1_subset_1(C_1377, k1_zfmisc_1(k2_zfmisc_1(A_1375, B_1376))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 25.04/15.47  tff(c_92274, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_92258])).
% 25.04/15.47  tff(c_70, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_145])).
% 25.04/15.47  tff(c_92275, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92274, c_70])).
% 25.04/15.47  tff(c_92780, plain, (![A_1395, B_1396, C_1397]: (k3_relset_1(A_1395, B_1396, C_1397)=k4_relat_1(C_1397) | ~m1_subset_1(C_1397, k1_zfmisc_1(k2_zfmisc_1(A_1395, B_1396))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 25.04/15.47  tff(c_92796, plain, (k3_relset_1('#skF_6', '#skF_7', '#skF_8')=k4_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_92780])).
% 25.04/15.47  tff(c_93234, plain, (![A_1420, B_1421, C_1422]: (m1_subset_1(k3_relset_1(A_1420, B_1421, C_1422), k1_zfmisc_1(k2_zfmisc_1(B_1421, A_1420))) | ~m1_subset_1(C_1422, k1_zfmisc_1(k2_zfmisc_1(A_1420, B_1421))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 25.04/15.47  tff(c_93258, plain, (m1_subset_1(k4_relat_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_92796, c_93234])).
% 25.04/15.47  tff(c_93269, plain, (m1_subset_1(k4_relat_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_93258])).
% 25.04/15.47  tff(c_60, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 25.04/15.47  tff(c_93292, plain, (k2_relset_1('#skF_7', '#skF_6', k4_relat_1('#skF_8'))=k2_relat_1(k4_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_93269, c_60])).
% 25.04/15.47  tff(c_93906, plain, (![B_1443, A_1444, C_1445]: (k2_relset_1(B_1443, A_1444, k3_relset_1(A_1444, B_1443, C_1445))=k1_relset_1(A_1444, B_1443, C_1445) | ~m1_subset_1(C_1445, k1_zfmisc_1(k2_zfmisc_1(A_1444, B_1443))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 25.04/15.47  tff(c_93926, plain, (k2_relset_1('#skF_7', '#skF_6', k3_relset_1('#skF_6', '#skF_7', '#skF_8'))=k1_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_93906])).
% 25.04/15.47  tff(c_93938, plain, (k2_relat_1(k4_relat_1('#skF_8'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_93292, c_92796, c_92274, c_93926])).
% 25.04/15.47  tff(c_46, plain, (![A_39]: (v1_xboole_0(k2_relat_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_86])).
% 25.04/15.47  tff(c_93958, plain, (v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_xboole_0(k4_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_93938, c_46])).
% 25.04/15.47  tff(c_93966, plain, (~v1_xboole_0(k4_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_93958])).
% 25.04/15.47  tff(c_48, plain, (![A_40, B_41]: (v1_relat_1(k2_zfmisc_1(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 25.04/15.47  tff(c_40, plain, (![B_36, A_34]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_76])).
% 25.04/15.47  tff(c_93287, plain, (v1_relat_1(k4_relat_1('#skF_8')) | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_93269, c_40])).
% 25.04/15.47  tff(c_93298, plain, (v1_relat_1(k4_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_93287])).
% 25.04/15.47  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 25.04/15.47  tff(c_58, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 25.04/15.47  tff(c_93293, plain, (k1_relset_1('#skF_7', '#skF_6', k4_relat_1('#skF_8'))=k1_relat_1(k4_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_93269, c_58])).
% 25.04/15.47  tff(c_56501, plain, (![A_803, B_804, C_805]: (k1_relset_1(A_803, B_804, C_805)=k1_relat_1(C_805) | ~m1_subset_1(C_805, k1_zfmisc_1(k2_zfmisc_1(A_803, B_804))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 25.04/15.47  tff(c_56517, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_56501])).
% 25.04/15.47  tff(c_56518, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56517, c_70])).
% 25.04/15.47  tff(c_56793, plain, (![A_816, B_817, C_818]: (k3_relset_1(A_816, B_817, C_818)=k4_relat_1(C_818) | ~m1_subset_1(C_818, k1_zfmisc_1(k2_zfmisc_1(A_816, B_817))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 25.04/15.47  tff(c_56809, plain, (k3_relset_1('#skF_6', '#skF_7', '#skF_8')=k4_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_56793])).
% 25.04/15.47  tff(c_58022, plain, (![A_861, B_862, C_863]: (m1_subset_1(k3_relset_1(A_861, B_862, C_863), k1_zfmisc_1(k2_zfmisc_1(B_862, A_861))) | ~m1_subset_1(C_863, k1_zfmisc_1(k2_zfmisc_1(A_861, B_862))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 25.04/15.47  tff(c_58046, plain, (m1_subset_1(k4_relat_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_56809, c_58022])).
% 25.04/15.47  tff(c_58057, plain, (m1_subset_1(k4_relat_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_58046])).
% 25.04/15.47  tff(c_62, plain, (![A_55, B_56, C_57]: (k3_relset_1(A_55, B_56, C_57)=k4_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 25.04/15.47  tff(c_58079, plain, (k3_relset_1('#skF_7', '#skF_6', k4_relat_1('#skF_8'))=k4_relat_1(k4_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_58057, c_62])).
% 25.04/15.47  tff(c_56, plain, (![A_46, B_47, C_48]: (m1_subset_1(k3_relset_1(A_46, B_47, C_48), k1_zfmisc_1(k2_zfmisc_1(B_47, A_46))) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 25.04/15.47  tff(c_58168, plain, (m1_subset_1(k4_relat_1(k4_relat_1('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~m1_subset_1(k4_relat_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_58079, c_56])).
% 25.04/15.47  tff(c_58172, plain, (m1_subset_1(k4_relat_1(k4_relat_1('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_58057, c_58168])).
% 25.04/15.47  tff(c_52, plain, (![C_45, B_44, A_43]: (v5_relat_1(C_45, B_44) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 25.04/15.47  tff(c_58207, plain, (v5_relat_1(k4_relat_1(k4_relat_1('#skF_8')), '#skF_7')), inference(resolution, [status(thm)], [c_58172, c_52])).
% 25.04/15.47  tff(c_58200, plain, (v1_relat_1(k4_relat_1(k4_relat_1('#skF_8'))) | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_58172, c_40])).
% 25.04/15.47  tff(c_58211, plain, (v1_relat_1(k4_relat_1(k4_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_58200])).
% 25.04/15.47  tff(c_58080, plain, (k1_relset_1('#skF_7', '#skF_6', k4_relat_1('#skF_8'))=k1_relat_1(k4_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_58057, c_58])).
% 25.04/15.47  tff(c_56399, plain, (![A_797, B_798, C_799]: (k2_relset_1(A_797, B_798, C_799)=k2_relat_1(C_799) | ~m1_subset_1(C_799, k1_zfmisc_1(k2_zfmisc_1(A_797, B_798))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 25.04/15.47  tff(c_56415, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_56399])).
% 25.04/15.47  tff(c_58441, plain, (![B_885, A_886, C_887]: (k1_relset_1(B_885, A_886, k3_relset_1(A_886, B_885, C_887))=k2_relset_1(A_886, B_885, C_887) | ~m1_subset_1(C_887, k1_zfmisc_1(k2_zfmisc_1(A_886, B_885))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 25.04/15.47  tff(c_58461, plain, (k1_relset_1('#skF_7', '#skF_6', k3_relset_1('#skF_6', '#skF_7', '#skF_8'))=k2_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_58441])).
% 25.04/15.47  tff(c_58473, plain, (k1_relat_1(k4_relat_1('#skF_8'))=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58080, c_56809, c_56415, c_58461])).
% 25.04/15.47  tff(c_58369, plain, (![B_881, A_882, C_883]: (k2_relset_1(B_881, A_882, k3_relset_1(A_882, B_881, C_883))=k1_relset_1(A_882, B_881, C_883) | ~m1_subset_1(C_883, k1_zfmisc_1(k2_zfmisc_1(A_882, B_881))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 25.04/15.47  tff(c_58373, plain, (k2_relset_1('#skF_6', '#skF_7', k3_relset_1('#skF_7', '#skF_6', k4_relat_1('#skF_8')))=k1_relset_1('#skF_7', '#skF_6', k4_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_58057, c_58369])).
% 25.04/15.47  tff(c_58392, plain, (k2_relset_1('#skF_6', '#skF_7', k4_relat_1(k4_relat_1('#skF_8')))=k1_relat_1(k4_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_58079, c_58080, c_58373])).
% 25.04/15.47  tff(c_58526, plain, (k2_relset_1('#skF_6', '#skF_7', k4_relat_1(k4_relat_1('#skF_8')))=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58473, c_58392])).
% 25.04/15.47  tff(c_36, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 25.04/15.47  tff(c_58212, plain, (r1_tarski(k4_relat_1(k4_relat_1('#skF_8')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_58172, c_36])).
% 25.04/15.47  tff(c_38, plain, (![A_32, B_33]: (m1_subset_1(A_32, k1_zfmisc_1(B_33)) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 25.04/15.47  tff(c_59647, plain, (![A_932, B_933, A_934]: (k2_relset_1(A_932, B_933, A_934)=k2_relat_1(A_934) | ~r1_tarski(A_934, k2_zfmisc_1(A_932, B_933)))), inference(resolution, [status(thm)], [c_38, c_56399])).
% 25.04/15.47  tff(c_59654, plain, (k2_relset_1('#skF_6', '#skF_7', k4_relat_1(k4_relat_1('#skF_8')))=k2_relat_1(k4_relat_1(k4_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_58212, c_59647])).
% 25.04/15.47  tff(c_59675, plain, (k2_relat_1(k4_relat_1(k4_relat_1('#skF_8')))=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58526, c_59654])).
% 25.04/15.47  tff(c_44, plain, (![B_38, A_37]: (r1_tarski(k2_relat_1(B_38), A_37) | ~v5_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_82])).
% 25.04/15.47  tff(c_59693, plain, (![A_37]: (r1_tarski(k2_relat_1('#skF_8'), A_37) | ~v5_relat_1(k4_relat_1(k4_relat_1('#skF_8')), A_37) | ~v1_relat_1(k4_relat_1(k4_relat_1('#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_59675, c_44])).
% 25.04/15.47  tff(c_61996, plain, (![A_970]: (r1_tarski(k2_relat_1('#skF_8'), A_970) | ~v5_relat_1(k4_relat_1(k4_relat_1('#skF_8')), A_970))), inference(demodulation, [status(thm), theory('equality')], [c_58211, c_59693])).
% 25.04/15.47  tff(c_62004, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_58207, c_61996])).
% 25.04/15.47  tff(c_58081, plain, (k2_relset_1('#skF_7', '#skF_6', k4_relat_1('#skF_8'))=k2_relat_1(k4_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_58057, c_60])).
% 25.04/15.47  tff(c_58389, plain, (k2_relset_1('#skF_7', '#skF_6', k3_relset_1('#skF_6', '#skF_7', '#skF_8'))=k1_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_58369])).
% 25.04/15.47  tff(c_58401, plain, (k2_relat_1(k4_relat_1('#skF_8'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58081, c_56809, c_56517, c_58389])).
% 25.04/15.47  tff(c_58418, plain, (v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_xboole_0(k4_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_58401, c_46])).
% 25.04/15.47  tff(c_58426, plain, (~v1_xboole_0(k4_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_58418])).
% 25.04/15.47  tff(c_58075, plain, (v1_relat_1(k4_relat_1('#skF_8')) | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_58057, c_40])).
% 25.04/15.47  tff(c_58086, plain, (v1_relat_1(k4_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_58075])).
% 25.04/15.47  tff(c_50, plain, (![A_42]: (~v1_xboole_0(k1_relat_1(A_42)) | ~v1_relat_1(A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_96])).
% 25.04/15.47  tff(c_58478, plain, (~v1_xboole_0(k2_relat_1('#skF_8')) | ~v1_relat_1(k4_relat_1('#skF_8')) | v1_xboole_0(k4_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_58473, c_50])).
% 25.04/15.47  tff(c_58482, plain, (~v1_xboole_0(k2_relat_1('#skF_8')) | v1_xboole_0(k4_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_58086, c_58478])).
% 25.04/15.47  tff(c_58483, plain, (~v1_xboole_0(k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_58426, c_58482])).
% 25.04/15.47  tff(c_30, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.04/15.47  tff(c_28, plain, (![A_26]: (k3_tarski(k1_zfmisc_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_52])).
% 25.04/15.47  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 25.04/15.47  tff(c_34, plain, (![A_30, B_31]: (r2_hidden(A_30, B_31) | v1_xboole_0(B_31) | ~m1_subset_1(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 25.04/15.47  tff(c_56011, plain, (![C_774, A_775, D_776]: (r2_hidden(C_774, k3_tarski(A_775)) | ~r2_hidden(D_776, A_775) | ~r2_hidden(C_774, D_776))), inference(cnfTransformation, [status(thm)], [f_50])).
% 25.04/15.47  tff(c_62596, plain, (![C_989, B_990, A_991]: (r2_hidden(C_989, k3_tarski(B_990)) | ~r2_hidden(C_989, A_991) | v1_xboole_0(B_990) | ~m1_subset_1(A_991, B_990))), inference(resolution, [status(thm)], [c_34, c_56011])).
% 25.04/15.47  tff(c_87505, plain, (![A_1293, B_1294]: (r2_hidden('#skF_1'(A_1293), k3_tarski(B_1294)) | v1_xboole_0(B_1294) | ~m1_subset_1(A_1293, B_1294) | v1_xboole_0(A_1293))), inference(resolution, [status(thm)], [c_4, c_62596])).
% 25.04/15.47  tff(c_87661, plain, (![A_1293, A_26]: (r2_hidden('#skF_1'(A_1293), A_26) | v1_xboole_0(k1_zfmisc_1(A_26)) | ~m1_subset_1(A_1293, k1_zfmisc_1(A_26)) | v1_xboole_0(A_1293))), inference(superposition, [status(thm), theory('equality')], [c_28, c_87505])).
% 25.04/15.47  tff(c_88081, plain, (![A_1301, A_1302]: (r2_hidden('#skF_1'(A_1301), A_1302) | ~m1_subset_1(A_1301, k1_zfmisc_1(A_1302)) | v1_xboole_0(A_1301))), inference(negUnitSimplification, [status(thm)], [c_30, c_87661])).
% 25.04/15.47  tff(c_32, plain, (![A_28, B_29]: (m1_subset_1(A_28, B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.04/15.47  tff(c_91522, plain, (![A_1327, A_1328]: (m1_subset_1('#skF_1'(A_1327), A_1328) | ~m1_subset_1(A_1327, k1_zfmisc_1(A_1328)) | v1_xboole_0(A_1327))), inference(resolution, [status(thm)], [c_88081, c_32])).
% 25.04/15.47  tff(c_163, plain, (![D_91]: (~r2_hidden(D_91, k2_relset_1('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1(D_91, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 25.04/15.47  tff(c_168, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_6', '#skF_7', '#skF_8')), '#skF_7') | v1_xboole_0(k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_4, c_163])).
% 25.04/15.47  tff(c_224, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_6', '#skF_7', '#skF_8')), '#skF_7')), inference(splitLeft, [status(thm)], [c_168])).
% 25.04/15.47  tff(c_56418, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_8')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56415, c_224])).
% 25.04/15.47  tff(c_91593, plain, (~m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | v1_xboole_0(k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_91522, c_56418])).
% 25.04/15.47  tff(c_91675, plain, (~m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_58483, c_91593])).
% 25.04/15.47  tff(c_91822, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_38, c_91675])).
% 25.04/15.47  tff(c_91826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62004, c_91822])).
% 25.04/15.47  tff(c_91827, plain, (v1_xboole_0(k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_58418])).
% 25.04/15.47  tff(c_91, plain, (![B_82, A_83]: (~v1_xboole_0(B_82) | B_82=A_83 | ~v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_40])).
% 25.04/15.47  tff(c_97, plain, (![A_83]: (k1_xboole_0=A_83 | ~v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_6, c_91])).
% 25.04/15.47  tff(c_91874, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_91827, c_97])).
% 25.04/15.47  tff(c_91902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56518, c_91874])).
% 25.04/15.47  tff(c_91903, plain, (v1_xboole_0(k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_168])).
% 25.04/15.47  tff(c_91917, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_91903, c_97])).
% 25.04/15.47  tff(c_93981, plain, (![B_1448, A_1449, C_1450]: (k1_relset_1(B_1448, A_1449, k3_relset_1(A_1449, B_1448, C_1450))=k2_relset_1(A_1449, B_1448, C_1450) | ~m1_subset_1(C_1450, k1_zfmisc_1(k2_zfmisc_1(A_1449, B_1448))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 25.04/15.47  tff(c_94001, plain, (k1_relset_1('#skF_7', '#skF_6', k3_relset_1('#skF_6', '#skF_7', '#skF_8'))=k2_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_93981])).
% 25.04/15.47  tff(c_94013, plain, (k1_relat_1(k4_relat_1('#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_93293, c_92796, c_91917, c_94001])).
% 25.04/15.47  tff(c_94018, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1('#skF_8')) | v1_xboole_0(k4_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_94013, c_50])).
% 25.04/15.47  tff(c_94022, plain, (v1_xboole_0(k4_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_93298, c_6, c_94018])).
% 25.04/15.47  tff(c_94024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93966, c_94022])).
% 25.04/15.47  tff(c_94025, plain, (v1_xboole_0(k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_93958])).
% 25.04/15.47  tff(c_94057, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_94025, c_97])).
% 25.04/15.47  tff(c_94077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92275, c_94057])).
% 25.04/15.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.04/15.47  
% 25.04/15.47  Inference rules
% 25.04/15.47  ----------------------
% 25.04/15.47  #Ref     : 0
% 25.04/15.47  #Sup     : 26041
% 25.04/15.47  #Fact    : 0
% 25.04/15.47  #Define  : 0
% 25.04/15.47  #Split   : 43
% 25.04/15.47  #Chain   : 0
% 25.04/15.47  #Close   : 0
% 25.04/15.48  
% 25.04/15.48  Ordering : KBO
% 25.04/15.48  
% 25.04/15.48  Simplification rules
% 25.04/15.48  ----------------------
% 25.04/15.48  #Subsume      : 9551
% 25.04/15.48  #Demod        : 13784
% 25.04/15.48  #Tautology    : 4151
% 25.04/15.48  #SimpNegUnit  : 1346
% 25.04/15.48  #BackRed      : 50
% 25.04/15.48  
% 25.04/15.48  #Partial instantiations: 0
% 25.04/15.48  #Strategies tried      : 1
% 25.04/15.48  
% 25.04/15.48  Timing (in seconds)
% 25.04/15.48  ----------------------
% 25.04/15.48  Preprocessing        : 0.35
% 25.04/15.48  Parsing              : 0.18
% 25.04/15.48  CNF conversion       : 0.03
% 25.04/15.48  Main loop            : 14.36
% 25.04/15.48  Inferencing          : 2.04
% 25.04/15.48  Reduction            : 4.23
% 25.04/15.48  Demodulation         : 3.10
% 25.04/15.48  BG Simplification    : 0.25
% 25.04/15.48  Subsumption          : 7.19
% 25.04/15.48  Abstraction          : 0.40
% 25.04/15.48  MUC search           : 0.00
% 25.04/15.48  Cooper               : 0.00
% 25.04/15.48  Total                : 14.76
% 25.04/15.48  Index Insertion      : 0.00
% 25.04/15.48  Index Deletion       : 0.00
% 25.04/15.48  Index Matching       : 0.00
% 25.04/15.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
