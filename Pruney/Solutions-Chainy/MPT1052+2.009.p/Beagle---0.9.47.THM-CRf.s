%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:09 EST 2020

% Result     : Theorem 12.92s
% Output     : CNFRefutation 13.15s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 405 expanded)
%              Number of leaves         :   37 ( 149 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 792 expanded)
%              Number of equality atoms :   49 ( 189 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_33,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_75,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_96962,plain,(
    ! [B_31737,A_31738] :
      ( r1_tarski(k2_relat_1(B_31737),A_31738)
      | ~ v5_relat_1(B_31737,A_31738)
      | ~ v1_relat_1(B_31737) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_70,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_88,plain,(
    ! [A_34,B_35] :
      ( v1_xboole_0(k1_funct_2(A_34,B_35))
      | ~ v1_xboole_0(B_35)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    ! [B_25,A_26] :
      ( ~ r2_hidden(B_25,A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_56])).

tff(c_99,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_60])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_6,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_66,plain,(
    ! [B_28,A_29] :
      ( ~ v1_xboole_0(B_28)
      | B_28 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,(
    ! [A_29] :
      ( k1_xboole_0 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_51,c_66])).

tff(c_102,plain,(
    ! [A_38,B_39] :
      ( k1_funct_2(A_38,B_39) = k1_xboole_0
      | ~ v1_xboole_0(B_39)
      | v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_88,c_69])).

tff(c_109,plain,(
    ! [A_40] :
      ( k1_funct_2(A_40,k1_xboole_0) = k1_xboole_0
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_51,c_102])).

tff(c_124,plain,(
    k1_funct_2('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_100])).

tff(c_36,plain,(
    ! [C_22,A_20,B_21] :
      ( m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ r2_hidden(C_22,k1_funct_2(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_7299,plain,(
    ! [C_2046,A_2047] :
      ( k1_xboole_0 = C_2046
      | ~ v1_funct_2(C_2046,A_2047,k1_xboole_0)
      | k1_xboole_0 = A_2047
      | ~ m1_subset_1(C_2046,k1_zfmisc_1(k2_zfmisc_1(A_2047,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34280,plain,(
    ! [C_11597,A_11598] :
      ( k1_xboole_0 = C_11597
      | ~ v1_funct_2(C_11597,A_11598,k1_xboole_0)
      | k1_xboole_0 = A_11598
      | ~ r2_hidden(C_11597,k1_funct_2(A_11598,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_36,c_7299])).

tff(c_34481,plain,(
    ! [C_11597] :
      ( k1_xboole_0 = C_11597
      | ~ v1_funct_2(C_11597,'#skF_3',k1_xboole_0)
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_11597,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_34280])).

tff(c_34493,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34481])).

tff(c_34557,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34493,c_51])).

tff(c_34560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_34557])).

tff(c_34562,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34481])).

tff(c_204,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_funct_2(C_51,A_52,B_53)
      | ~ r2_hidden(C_51,k1_funct_2(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_222,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_204])).

tff(c_6268,plain,(
    ! [A_1833,B_1834,C_1835] :
      ( k1_relset_1(A_1833,B_1834,C_1835) = k1_relat_1(C_1835)
      | ~ m1_subset_1(C_1835,k1_zfmisc_1(k2_zfmisc_1(A_1833,B_1834))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7460,plain,(
    ! [A_2118,B_2119,C_2120] :
      ( k1_relset_1(A_2118,B_2119,C_2120) = k1_relat_1(C_2120)
      | ~ r2_hidden(C_2120,k1_funct_2(A_2118,B_2119)) ) ),
    inference(resolution,[status(thm)],[c_36,c_6268])).

tff(c_7567,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_7460])).

tff(c_18489,plain,(
    ! [B_6257,A_6258,C_6259] :
      ( k1_xboole_0 = B_6257
      | k1_relset_1(A_6258,B_6257,C_6259) = A_6258
      | ~ v1_funct_2(C_6259,A_6258,B_6257)
      | ~ m1_subset_1(C_6259,k1_zfmisc_1(k2_zfmisc_1(A_6258,B_6257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_39844,plain,(
    ! [B_14707,A_14708,C_14709] :
      ( k1_xboole_0 = B_14707
      | k1_relset_1(A_14708,B_14707,C_14709) = A_14708
      | ~ v1_funct_2(C_14709,A_14708,B_14707)
      | ~ r2_hidden(C_14709,k1_funct_2(A_14708,B_14707)) ) ),
    inference(resolution,[status(thm)],[c_36,c_18489])).

tff(c_40059,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_39844])).

tff(c_40079,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_7567,c_40059])).

tff(c_40081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_34562,c_40079])).

tff(c_40083,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_40096,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40083,c_69])).

tff(c_40082,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_40089,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40082,c_69])).

tff(c_40106,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40096,c_40089])).

tff(c_40117,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40106,c_70])).

tff(c_40119,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40106,c_46])).

tff(c_40330,plain,(
    ! [C_14861,A_14862,B_14863] :
      ( v1_funct_2(C_14861,A_14862,B_14863)
      | ~ r2_hidden(C_14861,k1_funct_2(A_14862,B_14863)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40350,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_40119,c_40330])).

tff(c_45740,plain,(
    ! [A_16532,B_16533,C_16534] :
      ( k1_relset_1(A_16532,B_16533,C_16534) = k1_relat_1(C_16534)
      | ~ m1_subset_1(C_16534,k1_zfmisc_1(k2_zfmisc_1(A_16532,B_16533))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46623,plain,(
    ! [A_16710,B_16711,C_16712] :
      ( k1_relset_1(A_16710,B_16711,C_16712) = k1_relat_1(C_16712)
      | ~ r2_hidden(C_16712,k1_funct_2(A_16710,B_16711)) ) ),
    inference(resolution,[status(thm)],[c_36,c_45740])).

tff(c_46720,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40119,c_46623])).

tff(c_30,plain,(
    ! [B_16,C_17] :
      ( k1_relset_1(k1_xboole_0,B_16,C_17) = k1_xboole_0
      | ~ v1_funct_2(C_17,k1_xboole_0,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_55080,plain,(
    ! [B_19697,C_19698] :
      ( k1_relset_1('#skF_3',B_19697,C_19698) = '#skF_3'
      | ~ v1_funct_2(C_19698,'#skF_3',B_19697)
      | ~ m1_subset_1(C_19698,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_19697))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40096,c_40096,c_40096,c_40096,c_30])).

tff(c_96498,plain,(
    ! [B_31574,C_31575] :
      ( k1_relset_1('#skF_3',B_31574,C_31575) = '#skF_3'
      | ~ v1_funct_2(C_31575,'#skF_3',B_31574)
      | ~ r2_hidden(C_31575,k1_funct_2('#skF_3',B_31574)) ) ),
    inference(resolution,[status(thm)],[c_36,c_55080])).

tff(c_96781,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_40119,c_96498])).

tff(c_96800,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40350,c_46720,c_96781])).

tff(c_96802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40117,c_96800])).

tff(c_96803,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_96968,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96962,c_96803])).

tff(c_96972,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_96968])).

tff(c_97007,plain,(
    ! [C_31749,A_31750,B_31751] :
      ( m1_subset_1(C_31749,k1_zfmisc_1(k2_zfmisc_1(A_31750,B_31751)))
      | ~ r2_hidden(C_31749,k1_funct_2(A_31750,B_31751)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [C_11,B_10,A_9] :
      ( v5_relat_1(C_11,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_97016,plain,(
    ! [C_31752,B_31753,A_31754] :
      ( v5_relat_1(C_31752,B_31753)
      | ~ r2_hidden(C_31752,k1_funct_2(A_31754,B_31753)) ) ),
    inference(resolution,[status(thm)],[c_97007,c_16])).

tff(c_97032,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_97016])).

tff(c_97037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96972,c_97032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.92/5.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.08/5.59  
% 13.08/5.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.08/5.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 13.08/5.59  
% 13.08/5.59  %Foreground sorts:
% 13.08/5.59  
% 13.08/5.59  
% 13.08/5.59  %Background operators:
% 13.08/5.59  
% 13.08/5.59  
% 13.08/5.59  %Foreground operators:
% 13.08/5.59  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 13.08/5.59  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 13.08/5.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.08/5.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.08/5.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.08/5.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.08/5.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.08/5.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.08/5.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.08/5.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.08/5.59  tff('#skF_2', type, '#skF_2': $i).
% 13.08/5.59  tff('#skF_3', type, '#skF_3': $i).
% 13.08/5.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.08/5.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.08/5.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.08/5.59  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 13.08/5.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.08/5.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.08/5.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.08/5.59  tff('#skF_4', type, '#skF_4': $i).
% 13.08/5.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.08/5.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.08/5.59  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 13.08/5.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.08/5.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.08/5.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.08/5.59  
% 13.15/5.61  tff(f_103, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 13.15/5.61  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 13.15/5.61  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 13.15/5.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.15/5.61  tff(f_32, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_xboole_0)).
% 13.15/5.61  tff(f_33, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 13.15/5.61  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 13.15/5.61  tff(f_90, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 13.15/5.61  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.15/5.61  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.15/5.61  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.15/5.61  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.15/5.61  tff(c_96962, plain, (![B_31737, A_31738]: (r1_tarski(k2_relat_1(B_31737), A_31738) | ~v5_relat_1(B_31737, A_31738) | ~v1_relat_1(B_31737))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.15/5.61  tff(c_44, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.15/5.61  tff(c_70, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_44])).
% 13.15/5.61  tff(c_88, plain, (![A_34, B_35]: (v1_xboole_0(k1_funct_2(A_34, B_35)) | ~v1_xboole_0(B_35) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.15/5.61  tff(c_46, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.15/5.61  tff(c_56, plain, (![B_25, A_26]: (~r2_hidden(B_25, A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.15/5.61  tff(c_60, plain, (~v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_56])).
% 13.15/5.61  tff(c_99, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_88, c_60])).
% 13.15/5.61  tff(c_100, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_99])).
% 13.15/5.61  tff(c_6, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.15/5.61  tff(c_8, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.15/5.61  tff(c_51, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 13.15/5.61  tff(c_66, plain, (![B_28, A_29]: (~v1_xboole_0(B_28) | B_28=A_29 | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.15/5.61  tff(c_69, plain, (![A_29]: (k1_xboole_0=A_29 | ~v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_51, c_66])).
% 13.15/5.61  tff(c_102, plain, (![A_38, B_39]: (k1_funct_2(A_38, B_39)=k1_xboole_0 | ~v1_xboole_0(B_39) | v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_88, c_69])).
% 13.15/5.61  tff(c_109, plain, (![A_40]: (k1_funct_2(A_40, k1_xboole_0)=k1_xboole_0 | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_51, c_102])).
% 13.15/5.61  tff(c_124, plain, (k1_funct_2('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_100])).
% 13.15/5.61  tff(c_36, plain, (![C_22, A_20, B_21]: (m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~r2_hidden(C_22, k1_funct_2(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.15/5.61  tff(c_7299, plain, (![C_2046, A_2047]: (k1_xboole_0=C_2046 | ~v1_funct_2(C_2046, A_2047, k1_xboole_0) | k1_xboole_0=A_2047 | ~m1_subset_1(C_2046, k1_zfmisc_1(k2_zfmisc_1(A_2047, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.15/5.61  tff(c_34280, plain, (![C_11597, A_11598]: (k1_xboole_0=C_11597 | ~v1_funct_2(C_11597, A_11598, k1_xboole_0) | k1_xboole_0=A_11598 | ~r2_hidden(C_11597, k1_funct_2(A_11598, k1_xboole_0)))), inference(resolution, [status(thm)], [c_36, c_7299])).
% 13.15/5.61  tff(c_34481, plain, (![C_11597]: (k1_xboole_0=C_11597 | ~v1_funct_2(C_11597, '#skF_3', k1_xboole_0) | k1_xboole_0='#skF_3' | ~r2_hidden(C_11597, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_124, c_34280])).
% 13.15/5.61  tff(c_34493, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_34481])).
% 13.15/5.61  tff(c_34557, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34493, c_51])).
% 13.15/5.61  tff(c_34560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_34557])).
% 13.15/5.61  tff(c_34562, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34481])).
% 13.15/5.61  tff(c_204, plain, (![C_51, A_52, B_53]: (v1_funct_2(C_51, A_52, B_53) | ~r2_hidden(C_51, k1_funct_2(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.15/5.61  tff(c_222, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_204])).
% 13.15/5.61  tff(c_6268, plain, (![A_1833, B_1834, C_1835]: (k1_relset_1(A_1833, B_1834, C_1835)=k1_relat_1(C_1835) | ~m1_subset_1(C_1835, k1_zfmisc_1(k2_zfmisc_1(A_1833, B_1834))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.15/5.61  tff(c_7460, plain, (![A_2118, B_2119, C_2120]: (k1_relset_1(A_2118, B_2119, C_2120)=k1_relat_1(C_2120) | ~r2_hidden(C_2120, k1_funct_2(A_2118, B_2119)))), inference(resolution, [status(thm)], [c_36, c_6268])).
% 13.15/5.61  tff(c_7567, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_7460])).
% 13.15/5.61  tff(c_18489, plain, (![B_6257, A_6258, C_6259]: (k1_xboole_0=B_6257 | k1_relset_1(A_6258, B_6257, C_6259)=A_6258 | ~v1_funct_2(C_6259, A_6258, B_6257) | ~m1_subset_1(C_6259, k1_zfmisc_1(k2_zfmisc_1(A_6258, B_6257))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.15/5.61  tff(c_39844, plain, (![B_14707, A_14708, C_14709]: (k1_xboole_0=B_14707 | k1_relset_1(A_14708, B_14707, C_14709)=A_14708 | ~v1_funct_2(C_14709, A_14708, B_14707) | ~r2_hidden(C_14709, k1_funct_2(A_14708, B_14707)))), inference(resolution, [status(thm)], [c_36, c_18489])).
% 13.15/5.61  tff(c_40059, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_39844])).
% 13.15/5.61  tff(c_40079, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_222, c_7567, c_40059])).
% 13.15/5.61  tff(c_40081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_34562, c_40079])).
% 13.15/5.61  tff(c_40083, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_99])).
% 13.15/5.61  tff(c_40096, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_40083, c_69])).
% 13.15/5.61  tff(c_40082, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_99])).
% 13.15/5.61  tff(c_40089, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_40082, c_69])).
% 13.15/5.61  tff(c_40106, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40096, c_40089])).
% 13.15/5.61  tff(c_40117, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40106, c_70])).
% 13.15/5.61  tff(c_40119, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40106, c_46])).
% 13.15/5.61  tff(c_40330, plain, (![C_14861, A_14862, B_14863]: (v1_funct_2(C_14861, A_14862, B_14863) | ~r2_hidden(C_14861, k1_funct_2(A_14862, B_14863)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.15/5.61  tff(c_40350, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_40119, c_40330])).
% 13.15/5.61  tff(c_45740, plain, (![A_16532, B_16533, C_16534]: (k1_relset_1(A_16532, B_16533, C_16534)=k1_relat_1(C_16534) | ~m1_subset_1(C_16534, k1_zfmisc_1(k2_zfmisc_1(A_16532, B_16533))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.15/5.61  tff(c_46623, plain, (![A_16710, B_16711, C_16712]: (k1_relset_1(A_16710, B_16711, C_16712)=k1_relat_1(C_16712) | ~r2_hidden(C_16712, k1_funct_2(A_16710, B_16711)))), inference(resolution, [status(thm)], [c_36, c_45740])).
% 13.15/5.61  tff(c_46720, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40119, c_46623])).
% 13.15/5.61  tff(c_30, plain, (![B_16, C_17]: (k1_relset_1(k1_xboole_0, B_16, C_17)=k1_xboole_0 | ~v1_funct_2(C_17, k1_xboole_0, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.15/5.61  tff(c_55080, plain, (![B_19697, C_19698]: (k1_relset_1('#skF_3', B_19697, C_19698)='#skF_3' | ~v1_funct_2(C_19698, '#skF_3', B_19697) | ~m1_subset_1(C_19698, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_19697))))), inference(demodulation, [status(thm), theory('equality')], [c_40096, c_40096, c_40096, c_40096, c_30])).
% 13.15/5.61  tff(c_96498, plain, (![B_31574, C_31575]: (k1_relset_1('#skF_3', B_31574, C_31575)='#skF_3' | ~v1_funct_2(C_31575, '#skF_3', B_31574) | ~r2_hidden(C_31575, k1_funct_2('#skF_3', B_31574)))), inference(resolution, [status(thm)], [c_36, c_55080])).
% 13.15/5.61  tff(c_96781, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_40119, c_96498])).
% 13.15/5.61  tff(c_96800, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40350, c_46720, c_96781])).
% 13.15/5.61  tff(c_96802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40117, c_96800])).
% 13.15/5.61  tff(c_96803, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 13.15/5.61  tff(c_96968, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_96962, c_96803])).
% 13.15/5.61  tff(c_96972, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_96968])).
% 13.15/5.61  tff(c_97007, plain, (![C_31749, A_31750, B_31751]: (m1_subset_1(C_31749, k1_zfmisc_1(k2_zfmisc_1(A_31750, B_31751))) | ~r2_hidden(C_31749, k1_funct_2(A_31750, B_31751)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.15/5.61  tff(c_16, plain, (![C_11, B_10, A_9]: (v5_relat_1(C_11, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.15/5.61  tff(c_97016, plain, (![C_31752, B_31753, A_31754]: (v5_relat_1(C_31752, B_31753) | ~r2_hidden(C_31752, k1_funct_2(A_31754, B_31753)))), inference(resolution, [status(thm)], [c_97007, c_16])).
% 13.15/5.61  tff(c_97032, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_97016])).
% 13.15/5.61  tff(c_97037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96972, c_97032])).
% 13.15/5.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.15/5.61  
% 13.15/5.61  Inference rules
% 13.15/5.61  ----------------------
% 13.15/5.61  #Ref     : 0
% 13.15/5.61  #Sup     : 10780
% 13.15/5.61  #Fact    : 16
% 13.15/5.61  #Define  : 0
% 13.15/5.61  #Split   : 24
% 13.15/5.61  #Chain   : 0
% 13.15/5.61  #Close   : 0
% 13.15/5.61  
% 13.15/5.61  Ordering : KBO
% 13.15/5.61  
% 13.15/5.61  Simplification rules
% 13.15/5.61  ----------------------
% 13.15/5.61  #Subsume      : 6691
% 13.15/5.61  #Demod        : 2339
% 13.15/5.61  #Tautology    : 1230
% 13.15/5.61  #SimpNegUnit  : 694
% 13.15/5.61  #BackRed      : 130
% 13.15/5.61  
% 13.15/5.61  #Partial instantiations: 25760
% 13.15/5.61  #Strategies tried      : 1
% 13.15/5.61  
% 13.15/5.61  Timing (in seconds)
% 13.15/5.61  ----------------------
% 13.20/5.61  Preprocessing        : 0.33
% 13.20/5.61  Parsing              : 0.18
% 13.20/5.61  CNF conversion       : 0.02
% 13.20/5.61  Main loop            : 4.43
% 13.20/5.61  Inferencing          : 1.36
% 13.20/5.61  Reduction            : 0.91
% 13.20/5.61  Demodulation         : 0.62
% 13.20/5.61  BG Simplification    : 0.09
% 13.20/5.61  Subsumption          : 1.91
% 13.20/5.61  Abstraction          : 0.14
% 13.20/5.61  MUC search           : 0.00
% 13.20/5.61  Cooper               : 0.00
% 13.20/5.61  Total                : 4.80
% 13.20/5.61  Index Insertion      : 0.00
% 13.20/5.61  Index Deletion       : 0.00
% 13.20/5.61  Index Matching       : 0.00
% 13.20/5.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
