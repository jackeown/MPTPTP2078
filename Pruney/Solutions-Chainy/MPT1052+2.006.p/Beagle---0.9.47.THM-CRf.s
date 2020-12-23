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
% DateTime   : Thu Dec  3 10:17:09 EST 2020

% Result     : Theorem 8.65s
% Output     : CNFRefutation 9.08s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 231 expanded)
%              Number of leaves         :   38 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  145 ( 472 expanded)
%              Number of equality atoms :   35 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_92,axiom,(
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

tff(f_100,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22246,plain,(
    ! [B_6250,A_6251] :
      ( r1_tarski(k2_relat_1(B_6250),A_6251)
      | ~ v5_relat_1(B_6250,A_6251)
      | ~ v1_relat_1(B_6250) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_94,plain,(
    ! [A_41,B_42] :
      ( v1_xboole_0(k1_funct_2(A_41,B_42))
      | ~ v1_xboole_0(B_42)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_65,plain,(
    ! [B_33,A_34] :
      ( ~ r2_hidden(B_33,A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_65])).

tff(c_98,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_69])).

tff(c_99,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_56,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_75,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_335,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_funct_2(C_83,A_84,B_85)
      | ~ r2_hidden(C_83,k1_funct_2(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_358,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_335])).

tff(c_48,plain,(
    ! [C_29,A_27,B_28] :
      ( m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ r2_hidden(C_29,k1_funct_2(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_578,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12801,plain,(
    ! [A_4108,B_4109,C_4110] :
      ( k1_relset_1(A_4108,B_4109,C_4110) = k1_relat_1(C_4110)
      | ~ r2_hidden(C_4110,k1_funct_2(A_4108,B_4109)) ) ),
    inference(resolution,[status(thm)],[c_48,c_578])).

tff(c_12938,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_12801])).

tff(c_14398,plain,(
    ! [B_4544,A_4545,C_4546] :
      ( k1_xboole_0 = B_4544
      | k1_relset_1(A_4545,B_4544,C_4546) = A_4545
      | ~ v1_funct_2(C_4546,A_4545,B_4544)
      | ~ m1_subset_1(C_4546,k1_zfmisc_1(k2_zfmisc_1(A_4545,B_4544))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_21030,plain,(
    ! [B_6093,A_6094,C_6095] :
      ( k1_xboole_0 = B_6093
      | k1_relset_1(A_6094,B_6093,C_6095) = A_6094
      | ~ v1_funct_2(C_6095,A_6094,B_6093)
      | ~ r2_hidden(C_6095,k1_funct_2(A_6094,B_6093)) ) ),
    inference(resolution,[status(thm)],[c_48,c_14398])).

tff(c_21165,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_21030])).

tff(c_21185,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_12938,c_21165])).

tff(c_21186,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_21185])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_21273,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21186,c_12])).

tff(c_21275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_21273])).

tff(c_21277,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_21278,plain,(
    ! [A_6134,B_6135] :
      ( r2_hidden('#skF_2'(A_6134,B_6135),A_6134)
      | r1_tarski(A_6134,B_6135) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21287,plain,(
    ! [A_6134,B_6135] :
      ( ~ v1_xboole_0(A_6134)
      | r1_tarski(A_6134,B_6135) ) ),
    inference(resolution,[status(thm)],[c_21278,c_2])).

tff(c_21288,plain,(
    ! [A_6136,B_6137] :
      ( ~ v1_xboole_0(A_6136)
      | r1_tarski(A_6136,B_6137) ) ),
    inference(resolution,[status(thm)],[c_21278,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_21292,plain,(
    ! [B_6138,A_6139] :
      ( B_6138 = A_6139
      | ~ r1_tarski(B_6138,A_6139)
      | ~ v1_xboole_0(A_6139) ) ),
    inference(resolution,[status(thm)],[c_21288,c_14])).

tff(c_21302,plain,(
    ! [B_6140,A_6141] :
      ( B_6140 = A_6141
      | ~ v1_xboole_0(B_6140)
      | ~ v1_xboole_0(A_6141) ) ),
    inference(resolution,[status(thm)],[c_21287,c_21292])).

tff(c_21315,plain,(
    ! [A_6142] :
      ( k1_xboole_0 = A_6142
      | ~ v1_xboole_0(A_6142) ) ),
    inference(resolution,[status(thm)],[c_12,c_21302])).

tff(c_21328,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21277,c_21315])).

tff(c_21276,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_21329,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_21276,c_21315])).

tff(c_21347,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21328,c_21329])).

tff(c_21349,plain,(
    k1_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21347,c_75])).

tff(c_21351,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21347,c_58])).

tff(c_21933,plain,(
    ! [C_6212,A_6213,B_6214] :
      ( m1_subset_1(C_6212,k1_zfmisc_1(k2_zfmisc_1(A_6213,B_6214)))
      | ~ r2_hidden(C_6212,k1_funct_2(A_6213,B_6214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_21942,plain,(
    ! [C_6215,A_6216,B_6217] :
      ( v4_relat_1(C_6215,A_6216)
      | ~ r2_hidden(C_6215,k1_funct_2(A_6216,B_6217)) ) ),
    inference(resolution,[status(thm)],[c_21933,c_30])).

tff(c_21977,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_21351,c_21942])).

tff(c_21663,plain,(
    ! [B_6179,A_6180] :
      ( r1_tarski(k1_relat_1(B_6179),A_6180)
      | ~ v4_relat_1(B_6179,A_6180)
      | ~ v1_relat_1(B_6179) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_21291,plain,(
    ! [B_6137,A_6136] :
      ( B_6137 = A_6136
      | ~ r1_tarski(B_6137,A_6136)
      | ~ v1_xboole_0(A_6136) ) ),
    inference(resolution,[status(thm)],[c_21288,c_14])).

tff(c_21673,plain,(
    ! [B_6179,A_6180] :
      ( k1_relat_1(B_6179) = A_6180
      | ~ v1_xboole_0(A_6180)
      | ~ v4_relat_1(B_6179,A_6180)
      | ~ v1_relat_1(B_6179) ) ),
    inference(resolution,[status(thm)],[c_21663,c_21291])).

tff(c_21984,plain,
    ( k1_relat_1('#skF_5') = '#skF_4'
    | ~ v1_xboole_0('#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_21977,c_21673])).

tff(c_21990,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_21277,c_21984])).

tff(c_21992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21349,c_21990])).

tff(c_21993,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_22254,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22246,c_21993])).

tff(c_22259,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_22254])).

tff(c_22418,plain,(
    ! [C_6281,A_6282,B_6283] :
      ( m1_subset_1(C_6281,k1_zfmisc_1(k2_zfmisc_1(A_6282,B_6283)))
      | ~ r2_hidden(C_6281,k1_funct_2(A_6282,B_6283)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    ! [C_18,B_17,A_16] :
      ( v5_relat_1(C_18,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22484,plain,(
    ! [C_6291,B_6292,A_6293] :
      ( v5_relat_1(C_6291,B_6292)
      | ~ r2_hidden(C_6291,k1_funct_2(A_6293,B_6292)) ) ),
    inference(resolution,[status(thm)],[c_22418,c_28])).

tff(c_22510,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_22484])).

tff(c_22516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22259,c_22510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:39:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.65/2.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.65/2.88  
% 8.65/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.65/2.88  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 8.65/2.88  
% 8.65/2.88  %Foreground sorts:
% 8.65/2.88  
% 8.65/2.88  
% 8.65/2.88  %Background operators:
% 8.65/2.88  
% 8.65/2.88  
% 8.65/2.88  %Foreground operators:
% 8.65/2.88  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 8.65/2.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.65/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.65/2.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.65/2.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.65/2.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.65/2.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.65/2.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.65/2.88  tff('#skF_5', type, '#skF_5': $i).
% 8.65/2.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.65/2.88  tff('#skF_3', type, '#skF_3': $i).
% 8.65/2.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.65/2.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.65/2.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.65/2.88  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 8.65/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.65/2.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.65/2.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.65/2.88  tff('#skF_4', type, '#skF_4': $i).
% 8.65/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.65/2.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.65/2.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.65/2.88  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 8.65/2.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.65/2.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.65/2.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.65/2.88  
% 9.08/2.90  tff(f_113, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 9.08/2.90  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.08/2.90  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 9.08/2.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.08/2.90  tff(f_100, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 9.08/2.90  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.08/2.90  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.08/2.90  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.08/2.90  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.08/2.90  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.08/2.90  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.08/2.90  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.08/2.90  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.08/2.90  tff(c_22246, plain, (![B_6250, A_6251]: (r1_tarski(k2_relat_1(B_6250), A_6251) | ~v5_relat_1(B_6250, A_6251) | ~v1_relat_1(B_6250))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.08/2.90  tff(c_94, plain, (![A_41, B_42]: (v1_xboole_0(k1_funct_2(A_41, B_42)) | ~v1_xboole_0(B_42) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.08/2.90  tff(c_58, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.08/2.90  tff(c_65, plain, (![B_33, A_34]: (~r2_hidden(B_33, A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.08/2.90  tff(c_69, plain, (~v1_xboole_0(k1_funct_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_65])).
% 9.08/2.90  tff(c_98, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_94, c_69])).
% 9.08/2.90  tff(c_99, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_98])).
% 9.08/2.90  tff(c_56, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.08/2.90  tff(c_75, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_56])).
% 9.08/2.90  tff(c_335, plain, (![C_83, A_84, B_85]: (v1_funct_2(C_83, A_84, B_85) | ~r2_hidden(C_83, k1_funct_2(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.08/2.90  tff(c_358, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_335])).
% 9.08/2.90  tff(c_48, plain, (![C_29, A_27, B_28]: (m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~r2_hidden(C_29, k1_funct_2(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.08/2.90  tff(c_578, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.08/2.90  tff(c_12801, plain, (![A_4108, B_4109, C_4110]: (k1_relset_1(A_4108, B_4109, C_4110)=k1_relat_1(C_4110) | ~r2_hidden(C_4110, k1_funct_2(A_4108, B_4109)))), inference(resolution, [status(thm)], [c_48, c_578])).
% 9.08/2.90  tff(c_12938, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_12801])).
% 9.08/2.90  tff(c_14398, plain, (![B_4544, A_4545, C_4546]: (k1_xboole_0=B_4544 | k1_relset_1(A_4545, B_4544, C_4546)=A_4545 | ~v1_funct_2(C_4546, A_4545, B_4544) | ~m1_subset_1(C_4546, k1_zfmisc_1(k2_zfmisc_1(A_4545, B_4544))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.08/2.90  tff(c_21030, plain, (![B_6093, A_6094, C_6095]: (k1_xboole_0=B_6093 | k1_relset_1(A_6094, B_6093, C_6095)=A_6094 | ~v1_funct_2(C_6095, A_6094, B_6093) | ~r2_hidden(C_6095, k1_funct_2(A_6094, B_6093)))), inference(resolution, [status(thm)], [c_48, c_14398])).
% 9.08/2.90  tff(c_21165, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_21030])).
% 9.08/2.90  tff(c_21185, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_12938, c_21165])).
% 9.08/2.90  tff(c_21186, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_75, c_21185])).
% 9.08/2.90  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.08/2.90  tff(c_21273, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21186, c_12])).
% 9.08/2.90  tff(c_21275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_21273])).
% 9.08/2.90  tff(c_21277, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_98])).
% 9.08/2.90  tff(c_21278, plain, (![A_6134, B_6135]: (r2_hidden('#skF_2'(A_6134, B_6135), A_6134) | r1_tarski(A_6134, B_6135))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.08/2.90  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.08/2.90  tff(c_21287, plain, (![A_6134, B_6135]: (~v1_xboole_0(A_6134) | r1_tarski(A_6134, B_6135))), inference(resolution, [status(thm)], [c_21278, c_2])).
% 9.08/2.90  tff(c_21288, plain, (![A_6136, B_6137]: (~v1_xboole_0(A_6136) | r1_tarski(A_6136, B_6137))), inference(resolution, [status(thm)], [c_21278, c_2])).
% 9.08/2.90  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.08/2.90  tff(c_21292, plain, (![B_6138, A_6139]: (B_6138=A_6139 | ~r1_tarski(B_6138, A_6139) | ~v1_xboole_0(A_6139))), inference(resolution, [status(thm)], [c_21288, c_14])).
% 9.08/2.90  tff(c_21302, plain, (![B_6140, A_6141]: (B_6140=A_6141 | ~v1_xboole_0(B_6140) | ~v1_xboole_0(A_6141))), inference(resolution, [status(thm)], [c_21287, c_21292])).
% 9.08/2.90  tff(c_21315, plain, (![A_6142]: (k1_xboole_0=A_6142 | ~v1_xboole_0(A_6142))), inference(resolution, [status(thm)], [c_12, c_21302])).
% 9.08/2.90  tff(c_21328, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_21277, c_21315])).
% 9.08/2.90  tff(c_21276, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_98])).
% 9.08/2.90  tff(c_21329, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_21276, c_21315])).
% 9.08/2.90  tff(c_21347, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21328, c_21329])).
% 9.08/2.90  tff(c_21349, plain, (k1_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21347, c_75])).
% 9.08/2.90  tff(c_21351, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21347, c_58])).
% 9.08/2.90  tff(c_21933, plain, (![C_6212, A_6213, B_6214]: (m1_subset_1(C_6212, k1_zfmisc_1(k2_zfmisc_1(A_6213, B_6214))) | ~r2_hidden(C_6212, k1_funct_2(A_6213, B_6214)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.08/2.90  tff(c_30, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.08/2.90  tff(c_21942, plain, (![C_6215, A_6216, B_6217]: (v4_relat_1(C_6215, A_6216) | ~r2_hidden(C_6215, k1_funct_2(A_6216, B_6217)))), inference(resolution, [status(thm)], [c_21933, c_30])).
% 9.08/2.90  tff(c_21977, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_21351, c_21942])).
% 9.08/2.90  tff(c_21663, plain, (![B_6179, A_6180]: (r1_tarski(k1_relat_1(B_6179), A_6180) | ~v4_relat_1(B_6179, A_6180) | ~v1_relat_1(B_6179))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.08/2.90  tff(c_21291, plain, (![B_6137, A_6136]: (B_6137=A_6136 | ~r1_tarski(B_6137, A_6136) | ~v1_xboole_0(A_6136))), inference(resolution, [status(thm)], [c_21288, c_14])).
% 9.08/2.90  tff(c_21673, plain, (![B_6179, A_6180]: (k1_relat_1(B_6179)=A_6180 | ~v1_xboole_0(A_6180) | ~v4_relat_1(B_6179, A_6180) | ~v1_relat_1(B_6179))), inference(resolution, [status(thm)], [c_21663, c_21291])).
% 9.08/2.90  tff(c_21984, plain, (k1_relat_1('#skF_5')='#skF_4' | ~v1_xboole_0('#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_21977, c_21673])).
% 9.08/2.90  tff(c_21990, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_21277, c_21984])).
% 9.08/2.90  tff(c_21992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21349, c_21990])).
% 9.08/2.90  tff(c_21993, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 9.08/2.90  tff(c_22254, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22246, c_21993])).
% 9.08/2.90  tff(c_22259, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_22254])).
% 9.08/2.90  tff(c_22418, plain, (![C_6281, A_6282, B_6283]: (m1_subset_1(C_6281, k1_zfmisc_1(k2_zfmisc_1(A_6282, B_6283))) | ~r2_hidden(C_6281, k1_funct_2(A_6282, B_6283)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.08/2.90  tff(c_28, plain, (![C_18, B_17, A_16]: (v5_relat_1(C_18, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.08/2.90  tff(c_22484, plain, (![C_6291, B_6292, A_6293]: (v5_relat_1(C_6291, B_6292) | ~r2_hidden(C_6291, k1_funct_2(A_6293, B_6292)))), inference(resolution, [status(thm)], [c_22418, c_28])).
% 9.08/2.90  tff(c_22510, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_22484])).
% 9.08/2.90  tff(c_22516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22259, c_22510])).
% 9.08/2.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.08/2.90  
% 9.08/2.90  Inference rules
% 9.08/2.90  ----------------------
% 9.08/2.90  #Ref     : 0
% 9.08/2.90  #Sup     : 2731
% 9.08/2.90  #Fact    : 4
% 9.08/2.90  #Define  : 0
% 9.08/2.90  #Split   : 12
% 9.08/2.90  #Chain   : 0
% 9.08/2.90  #Close   : 0
% 9.08/2.90  
% 9.08/2.90  Ordering : KBO
% 9.08/2.90  
% 9.08/2.90  Simplification rules
% 9.08/2.90  ----------------------
% 9.08/2.90  #Subsume      : 967
% 9.08/2.90  #Demod        : 688
% 9.08/2.90  #Tautology    : 483
% 9.08/2.90  #SimpNegUnit  : 41
% 9.08/2.90  #BackRed      : 172
% 9.08/2.90  
% 9.08/2.90  #Partial instantiations: 4284
% 9.08/2.90  #Strategies tried      : 1
% 9.08/2.90  
% 9.08/2.90  Timing (in seconds)
% 9.08/2.90  ----------------------
% 9.08/2.90  Preprocessing        : 0.33
% 9.08/2.90  Parsing              : 0.17
% 9.08/2.90  CNF conversion       : 0.02
% 9.08/2.90  Main loop            : 1.81
% 9.08/2.90  Inferencing          : 0.69
% 9.08/2.90  Reduction            : 0.42
% 9.08/2.90  Demodulation         : 0.28
% 9.08/2.90  BG Simplification    : 0.06
% 9.08/2.90  Subsumption          : 0.52
% 9.08/2.90  Abstraction          : 0.07
% 9.08/2.90  MUC search           : 0.00
% 9.08/2.90  Cooper               : 0.00
% 9.08/2.90  Total                : 2.17
% 9.08/2.90  Index Insertion      : 0.00
% 9.08/2.90  Index Deletion       : 0.00
% 9.08/2.90  Index Matching       : 0.00
% 9.08/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
