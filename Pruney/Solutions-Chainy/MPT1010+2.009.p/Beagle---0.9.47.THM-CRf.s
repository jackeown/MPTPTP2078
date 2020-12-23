%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:06 EST 2020

% Result     : Theorem 9.29s
% Output     : CNFRefutation 9.29s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 112 expanded)
%              Number of leaves         :   45 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 215 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_82,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_320,plain,(
    ! [C_99,B_100,A_101] :
      ( v5_relat_1(C_99,B_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_329,plain,(
    v5_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_82,c_320])).

tff(c_80,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_236,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_245,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_236])).

tff(c_86,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_84,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_720,plain,(
    ! [A_153,B_154,C_155] :
      ( k1_relset_1(A_153,B_154,C_155) = k1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_734,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_720])).

tff(c_1225,plain,(
    ! [B_204,A_205,C_206] :
      ( k1_xboole_0 = B_204
      | k1_relset_1(A_205,B_204,C_206) = A_205
      | ~ v1_funct_2(C_206,A_205,B_204)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_205,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1236,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_82,c_1225])).

tff(c_1241,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_734,c_1236])).

tff(c_1242,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1241])).

tff(c_52,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k2_relat_1(B_28),A_27)
      | ~ v5_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_901,plain,(
    ! [B_172,A_173] :
      ( r2_hidden(k1_funct_1(B_172,A_173),k2_relat_1(B_172))
      | ~ r2_hidden(A_173,k1_relat_1(B_172))
      | ~ v1_funct_1(B_172)
      | ~ v1_relat_1(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_375,plain,(
    ! [A_111,C_112,B_113] :
      ( m1_subset_1(A_111,C_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(C_112))
      | ~ r2_hidden(A_111,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_380,plain,(
    ! [A_111,B_23,A_22] :
      ( m1_subset_1(A_111,B_23)
      | ~ r2_hidden(A_111,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_46,c_375])).

tff(c_19538,plain,(
    ! [B_56142,A_56143,B_56144] :
      ( m1_subset_1(k1_funct_1(B_56142,A_56143),B_56144)
      | ~ r1_tarski(k2_relat_1(B_56142),B_56144)
      | ~ r2_hidden(A_56143,k1_relat_1(B_56142))
      | ~ v1_funct_1(B_56142)
      | ~ v1_relat_1(B_56142) ) ),
    inference(resolution,[status(thm)],[c_901,c_380])).

tff(c_19548,plain,(
    ! [B_56307,A_56308,A_56309] :
      ( m1_subset_1(k1_funct_1(B_56307,A_56308),A_56309)
      | ~ r2_hidden(A_56308,k1_relat_1(B_56307))
      | ~ v1_funct_1(B_56307)
      | ~ v5_relat_1(B_56307,A_56309)
      | ~ v1_relat_1(B_56307) ) ),
    inference(resolution,[status(thm)],[c_52,c_19538])).

tff(c_19562,plain,(
    ! [A_56308,A_56309] :
      ( m1_subset_1(k1_funct_1('#skF_9',A_56308),A_56309)
      | ~ r2_hidden(A_56308,'#skF_6')
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_56309)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1242,c_19548])).

tff(c_19583,plain,(
    ! [A_56472,A_56473] :
      ( m1_subset_1(k1_funct_1('#skF_9',A_56472),A_56473)
      | ~ r2_hidden(A_56472,'#skF_6')
      | ~ v5_relat_1('#skF_9',A_56473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_86,c_19562])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_103,plain,(
    ! [B_50,A_51] :
      ( ~ r2_hidden(B_50,A_51)
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [C_10] : ~ v1_xboole_0(k1_tarski(C_10)) ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_220,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,B_76)
      | v1_xboole_0(B_76)
      | ~ m1_subset_1(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_224,plain,(
    ! [A_75,A_6] :
      ( A_75 = A_6
      | v1_xboole_0(k1_tarski(A_6))
      | ~ m1_subset_1(A_75,k1_tarski(A_6)) ) ),
    inference(resolution,[status(thm)],[c_220,c_8])).

tff(c_233,plain,(
    ! [A_75,A_6] :
      ( A_75 = A_6
      | ~ m1_subset_1(A_75,k1_tarski(A_6)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_224])).

tff(c_19670,plain,(
    ! [A_56636,A_56637] :
      ( k1_funct_1('#skF_9',A_56636) = A_56637
      | ~ r2_hidden(A_56636,'#skF_6')
      | ~ v5_relat_1('#skF_9',k1_tarski(A_56637)) ) ),
    inference(resolution,[status(thm)],[c_19583,c_233])).

tff(c_19713,plain,(
    ! [A_56800] :
      ( k1_funct_1('#skF_9','#skF_8') = A_56800
      | ~ v5_relat_1('#skF_9',k1_tarski(A_56800)) ) ),
    inference(resolution,[status(thm)],[c_80,c_19670])).

tff(c_19725,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_329,c_19713])).

tff(c_19729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_19725])).

tff(c_19730,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1241])).

tff(c_134,plain,(
    ! [B_58,A_59] :
      ( ~ r1_tarski(B_58,A_59)
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_153,plain,(
    ! [C_10] : ~ r1_tarski(k1_tarski(C_10),C_10) ),
    inference(resolution,[status(thm)],[c_10,c_134])).

tff(c_19757,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_19730,c_153])).

tff(c_19774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_19757])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.29/3.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.29/3.45  
% 9.29/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.29/3.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2
% 9.29/3.45  
% 9.29/3.45  %Foreground sorts:
% 9.29/3.45  
% 9.29/3.45  
% 9.29/3.45  %Background operators:
% 9.29/3.45  
% 9.29/3.45  
% 9.29/3.45  %Foreground operators:
% 9.29/3.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.29/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.29/3.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.29/3.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.29/3.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.29/3.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.29/3.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.29/3.45  tff('#skF_7', type, '#skF_7': $i).
% 9.29/3.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.29/3.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.29/3.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.29/3.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.29/3.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.29/3.45  tff('#skF_6', type, '#skF_6': $i).
% 9.29/3.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.29/3.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.29/3.45  tff('#skF_9', type, '#skF_9': $i).
% 9.29/3.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.29/3.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.29/3.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.29/3.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.29/3.45  tff('#skF_8', type, '#skF_8': $i).
% 9.29/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.29/3.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.29/3.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.29/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.29/3.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.29/3.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.29/3.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.29/3.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.29/3.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.29/3.45  
% 9.29/3.47  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.29/3.47  tff(f_131, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 9.29/3.47  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.29/3.47  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.29/3.47  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.29/3.47  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.29/3.47  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.29/3.47  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 9.29/3.47  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.29/3.47  tff(f_69, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 9.29/3.47  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.29/3.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.29/3.47  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.29/3.47  tff(f_88, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.29/3.47  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.29/3.47  tff(c_78, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.29/3.47  tff(c_82, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.29/3.47  tff(c_320, plain, (![C_99, B_100, A_101]: (v5_relat_1(C_99, B_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.29/3.47  tff(c_329, plain, (v5_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_82, c_320])).
% 9.29/3.47  tff(c_80, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.29/3.47  tff(c_236, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.29/3.47  tff(c_245, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_82, c_236])).
% 9.29/3.47  tff(c_86, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.29/3.47  tff(c_84, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.29/3.47  tff(c_720, plain, (![A_153, B_154, C_155]: (k1_relset_1(A_153, B_154, C_155)=k1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.29/3.47  tff(c_734, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_82, c_720])).
% 9.29/3.47  tff(c_1225, plain, (![B_204, A_205, C_206]: (k1_xboole_0=B_204 | k1_relset_1(A_205, B_204, C_206)=A_205 | ~v1_funct_2(C_206, A_205, B_204) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_205, B_204))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.29/3.47  tff(c_1236, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_82, c_1225])).
% 9.29/3.47  tff(c_1241, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_734, c_1236])).
% 9.29/3.47  tff(c_1242, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_1241])).
% 9.29/3.47  tff(c_52, plain, (![B_28, A_27]: (r1_tarski(k2_relat_1(B_28), A_27) | ~v5_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.29/3.47  tff(c_901, plain, (![B_172, A_173]: (r2_hidden(k1_funct_1(B_172, A_173), k2_relat_1(B_172)) | ~r2_hidden(A_173, k1_relat_1(B_172)) | ~v1_funct_1(B_172) | ~v1_relat_1(B_172))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.29/3.47  tff(c_46, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.29/3.47  tff(c_375, plain, (![A_111, C_112, B_113]: (m1_subset_1(A_111, C_112) | ~m1_subset_1(B_113, k1_zfmisc_1(C_112)) | ~r2_hidden(A_111, B_113))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.29/3.47  tff(c_380, plain, (![A_111, B_23, A_22]: (m1_subset_1(A_111, B_23) | ~r2_hidden(A_111, A_22) | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_46, c_375])).
% 9.29/3.47  tff(c_19538, plain, (![B_56142, A_56143, B_56144]: (m1_subset_1(k1_funct_1(B_56142, A_56143), B_56144) | ~r1_tarski(k2_relat_1(B_56142), B_56144) | ~r2_hidden(A_56143, k1_relat_1(B_56142)) | ~v1_funct_1(B_56142) | ~v1_relat_1(B_56142))), inference(resolution, [status(thm)], [c_901, c_380])).
% 9.29/3.47  tff(c_19548, plain, (![B_56307, A_56308, A_56309]: (m1_subset_1(k1_funct_1(B_56307, A_56308), A_56309) | ~r2_hidden(A_56308, k1_relat_1(B_56307)) | ~v1_funct_1(B_56307) | ~v5_relat_1(B_56307, A_56309) | ~v1_relat_1(B_56307))), inference(resolution, [status(thm)], [c_52, c_19538])).
% 9.29/3.47  tff(c_19562, plain, (![A_56308, A_56309]: (m1_subset_1(k1_funct_1('#skF_9', A_56308), A_56309) | ~r2_hidden(A_56308, '#skF_6') | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_56309) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1242, c_19548])).
% 9.29/3.47  tff(c_19583, plain, (![A_56472, A_56473]: (m1_subset_1(k1_funct_1('#skF_9', A_56472), A_56473) | ~r2_hidden(A_56472, '#skF_6') | ~v5_relat_1('#skF_9', A_56473))), inference(demodulation, [status(thm), theory('equality')], [c_245, c_86, c_19562])).
% 9.29/3.47  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.29/3.47  tff(c_103, plain, (![B_50, A_51]: (~r2_hidden(B_50, A_51) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.29/3.47  tff(c_114, plain, (![C_10]: (~v1_xboole_0(k1_tarski(C_10)))), inference(resolution, [status(thm)], [c_10, c_103])).
% 9.29/3.47  tff(c_220, plain, (![A_75, B_76]: (r2_hidden(A_75, B_76) | v1_xboole_0(B_76) | ~m1_subset_1(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.29/3.47  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.29/3.47  tff(c_224, plain, (![A_75, A_6]: (A_75=A_6 | v1_xboole_0(k1_tarski(A_6)) | ~m1_subset_1(A_75, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_220, c_8])).
% 9.29/3.47  tff(c_233, plain, (![A_75, A_6]: (A_75=A_6 | ~m1_subset_1(A_75, k1_tarski(A_6)))), inference(negUnitSimplification, [status(thm)], [c_114, c_224])).
% 9.29/3.47  tff(c_19670, plain, (![A_56636, A_56637]: (k1_funct_1('#skF_9', A_56636)=A_56637 | ~r2_hidden(A_56636, '#skF_6') | ~v5_relat_1('#skF_9', k1_tarski(A_56637)))), inference(resolution, [status(thm)], [c_19583, c_233])).
% 9.29/3.47  tff(c_19713, plain, (![A_56800]: (k1_funct_1('#skF_9', '#skF_8')=A_56800 | ~v5_relat_1('#skF_9', k1_tarski(A_56800)))), inference(resolution, [status(thm)], [c_80, c_19670])).
% 9.29/3.47  tff(c_19725, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_329, c_19713])).
% 9.29/3.47  tff(c_19729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_19725])).
% 9.29/3.47  tff(c_19730, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1241])).
% 9.29/3.47  tff(c_134, plain, (![B_58, A_59]: (~r1_tarski(B_58, A_59) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.29/3.47  tff(c_153, plain, (![C_10]: (~r1_tarski(k1_tarski(C_10), C_10))), inference(resolution, [status(thm)], [c_10, c_134])).
% 9.29/3.47  tff(c_19757, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_19730, c_153])).
% 9.29/3.47  tff(c_19774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_19757])).
% 9.29/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.29/3.47  
% 9.29/3.47  Inference rules
% 9.29/3.47  ----------------------
% 9.29/3.47  #Ref     : 0
% 9.29/3.47  #Sup     : 2098
% 9.29/3.47  #Fact    : 24
% 9.29/3.47  #Define  : 0
% 9.29/3.47  #Split   : 20
% 9.29/3.47  #Chain   : 0
% 9.29/3.47  #Close   : 0
% 9.29/3.47  
% 9.29/3.47  Ordering : KBO
% 9.29/3.47  
% 9.29/3.47  Simplification rules
% 9.29/3.47  ----------------------
% 9.29/3.47  #Subsume      : 439
% 9.29/3.47  #Demod        : 812
% 9.29/3.47  #Tautology    : 596
% 9.29/3.47  #SimpNegUnit  : 141
% 9.29/3.47  #BackRed      : 8
% 9.29/3.47  
% 9.29/3.47  #Partial instantiations: 32104
% 9.29/3.47  #Strategies tried      : 1
% 9.29/3.47  
% 9.29/3.47  Timing (in seconds)
% 9.29/3.47  ----------------------
% 9.29/3.47  Preprocessing        : 0.34
% 9.29/3.47  Parsing              : 0.18
% 9.29/3.47  CNF conversion       : 0.03
% 9.29/3.47  Main loop            : 2.36
% 9.29/3.47  Inferencing          : 1.07
% 9.29/3.47  Reduction            : 0.69
% 9.29/3.47  Demodulation         : 0.49
% 9.29/3.47  BG Simplification    : 0.07
% 9.29/3.47  Subsumption          : 0.39
% 9.29/3.47  Abstraction          : 0.09
% 9.29/3.47  MUC search           : 0.00
% 9.29/3.47  Cooper               : 0.00
% 9.29/3.47  Total                : 2.73
% 9.29/3.47  Index Insertion      : 0.00
% 9.29/3.47  Index Deletion       : 0.00
% 9.29/3.47  Index Matching       : 0.00
% 9.29/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
