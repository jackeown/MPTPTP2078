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
% DateTime   : Thu Dec  3 10:18:09 EST 2020

% Result     : Theorem 8.57s
% Output     : CNFRefutation 8.57s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 713 expanded)
%              Number of leaves         :   43 ( 266 expanded)
%              Depth                    :   25
%              Number of atoms          :  206 (2295 expanded)
%              Number of equality atoms :   38 ( 427 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_160,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_138,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_22,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_132,plain,(
    ! [B_100,A_101] :
      ( v1_relat_1(B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_101))
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_138,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_132])).

tff(c_142,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_138])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4710,plain,(
    ! [A_471,B_472,C_473] :
      ( k2_relset_1(A_471,B_472,C_473) = k2_relat_1(C_473)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(A_471,B_472))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4725,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_4710])).

tff(c_76,plain,(
    ~ r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4726,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4725,c_76])).

tff(c_4733,plain,
    ( ~ v5_relat_1('#skF_9','#skF_6')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_20,c_4726])).

tff(c_4736,plain,(
    ~ v5_relat_1('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_4733])).

tff(c_84,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_82,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4791,plain,(
    ! [A_483,B_484,C_485] :
      ( k1_relset_1(A_483,B_484,C_485) = k1_relat_1(C_485)
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(A_483,B_484))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4811,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_4791])).

tff(c_5303,plain,(
    ! [B_581,A_582,C_583] :
      ( k1_xboole_0 = B_581
      | k1_relset_1(A_582,B_581,C_583) = A_582
      | ~ v1_funct_2(C_583,A_582,B_581)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(A_582,B_581))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5314,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_5303])).

tff(c_5325,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4811,c_5314])).

tff(c_5327,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_5325])).

tff(c_5977,plain,(
    ! [C_632,B_633] :
      ( r2_hidden('#skF_5'(k1_relat_1(C_632),B_633,C_632),k1_relat_1(C_632))
      | m1_subset_1(C_632,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_632),B_633)))
      | ~ v1_funct_1(C_632)
      | ~ v1_relat_1(C_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5985,plain,(
    ! [B_633] :
      ( r2_hidden('#skF_5'('#skF_7',B_633,'#skF_9'),k1_relat_1('#skF_9'))
      | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_9'),B_633)))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5327,c_5977])).

tff(c_5995,plain,(
    ! [B_634] :
      ( r2_hidden('#skF_5'('#skF_7',B_634,'#skF_9'),'#skF_7')
      | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_634))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_84,c_5327,c_5327,c_5985])).

tff(c_42,plain,(
    ! [C_60,B_59,A_58] :
      ( v5_relat_1(C_60,B_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6039,plain,(
    ! [B_635] :
      ( v5_relat_1('#skF_9',B_635)
      | r2_hidden('#skF_5'('#skF_7',B_635,'#skF_9'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5995,c_42])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6050,plain,(
    ! [B_635] :
      ( m1_subset_1('#skF_5'('#skF_7',B_635,'#skF_9'),'#skF_7')
      | v5_relat_1('#skF_9',B_635) ) ),
    inference(resolution,[status(thm)],[c_6039,c_10])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_6738,plain,(
    ! [A_694,B_695,C_696,D_697] :
      ( k3_funct_2(A_694,B_695,C_696,D_697) = k1_funct_1(C_696,D_697)
      | ~ m1_subset_1(D_697,A_694)
      | ~ m1_subset_1(C_696,k1_zfmisc_1(k2_zfmisc_1(A_694,B_695)))
      | ~ v1_funct_2(C_696,A_694,B_695)
      | ~ v1_funct_1(C_696)
      | v1_xboole_0(A_694) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6750,plain,(
    ! [B_695,C_696,B_635] :
      ( k3_funct_2('#skF_7',B_695,C_696,'#skF_5'('#skF_7',B_635,'#skF_9')) = k1_funct_1(C_696,'#skF_5'('#skF_7',B_635,'#skF_9'))
      | ~ m1_subset_1(C_696,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_695)))
      | ~ v1_funct_2(C_696,'#skF_7',B_695)
      | ~ v1_funct_1(C_696)
      | v1_xboole_0('#skF_7')
      | v5_relat_1('#skF_9',B_635) ) ),
    inference(resolution,[status(thm)],[c_6050,c_6738])).

tff(c_7227,plain,(
    ! [B_710,C_711,B_712] :
      ( k3_funct_2('#skF_7',B_710,C_711,'#skF_5'('#skF_7',B_712,'#skF_9')) = k1_funct_1(C_711,'#skF_5'('#skF_7',B_712,'#skF_9'))
      | ~ m1_subset_1(C_711,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_710)))
      | ~ v1_funct_2(C_711,'#skF_7',B_710)
      | ~ v1_funct_1(C_711)
      | v5_relat_1('#skF_9',B_712) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6750])).

tff(c_7261,plain,(
    ! [B_712] :
      ( k3_funct_2('#skF_7','#skF_8','#skF_9','#skF_5'('#skF_7',B_712,'#skF_9')) = k1_funct_1('#skF_9','#skF_5'('#skF_7',B_712,'#skF_9'))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
      | ~ v1_funct_1('#skF_9')
      | v5_relat_1('#skF_9',B_712) ) ),
    inference(resolution,[status(thm)],[c_80,c_7227])).

tff(c_8449,plain,(
    ! [B_773] :
      ( k3_funct_2('#skF_7','#skF_8','#skF_9','#skF_5'('#skF_7',B_773,'#skF_9')) = k1_funct_1('#skF_9','#skF_5'('#skF_7',B_773,'#skF_9'))
      | v5_relat_1('#skF_9',B_773) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_7261])).

tff(c_78,plain,(
    ! [E_89] :
      ( r2_hidden(k3_funct_2('#skF_7','#skF_8','#skF_9',E_89),'#skF_6')
      | ~ m1_subset_1(E_89,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_8651,plain,(
    ! [B_778] :
      ( r2_hidden(k1_funct_1('#skF_9','#skF_5'('#skF_7',B_778,'#skF_9')),'#skF_6')
      | ~ m1_subset_1('#skF_5'('#skF_7',B_778,'#skF_9'),'#skF_7')
      | v5_relat_1('#skF_9',B_778) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8449,c_78])).

tff(c_5892,plain,(
    ! [C_626,B_627] :
      ( ~ r2_hidden(k1_funct_1(C_626,'#skF_5'(k1_relat_1(C_626),B_627,C_626)),B_627)
      | v1_funct_2(C_626,k1_relat_1(C_626),B_627)
      | ~ v1_funct_1(C_626)
      | ~ v1_relat_1(C_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5895,plain,(
    ! [B_627] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_5'('#skF_7',B_627,'#skF_9')),B_627)
      | v1_funct_2('#skF_9',k1_relat_1('#skF_9'),B_627)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5327,c_5892])).

tff(c_5901,plain,(
    ! [B_627] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_5'('#skF_7',B_627,'#skF_9')),B_627)
      | v1_funct_2('#skF_9','#skF_7',B_627) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_84,c_5327,c_5895])).

tff(c_8659,plain,
    ( v1_funct_2('#skF_9','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_9'),'#skF_7')
    | v5_relat_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_8651,c_5901])).

tff(c_8670,plain,
    ( v1_funct_2('#skF_9','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_9'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_4736,c_8659])).

tff(c_8673,plain,(
    ~ m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_8670])).

tff(c_8686,plain,(
    v5_relat_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_6050,c_8673])).

tff(c_8701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4736,c_8686])).

tff(c_8703,plain,(
    m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_8670])).

tff(c_62,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k3_funct_2(A_70,B_71,C_72,D_73) = k1_funct_1(C_72,D_73)
      | ~ m1_subset_1(D_73,A_70)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_2(C_72,A_70,B_71)
      | ~ v1_funct_1(C_72)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8705,plain,(
    ! [B_71,C_72] :
      ( k3_funct_2('#skF_7',B_71,C_72,'#skF_5'('#skF_7','#skF_6','#skF_9')) = k1_funct_1(C_72,'#skF_5'('#skF_7','#skF_6','#skF_9'))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_71)))
      | ~ v1_funct_2(C_72,'#skF_7',B_71)
      | ~ v1_funct_1(C_72)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8703,c_62])).

tff(c_8722,plain,(
    ! [B_782,C_783] :
      ( k3_funct_2('#skF_7',B_782,C_783,'#skF_5'('#skF_7','#skF_6','#skF_9')) = k1_funct_1(C_783,'#skF_5'('#skF_7','#skF_6','#skF_9'))
      | ~ m1_subset_1(C_783,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_782)))
      | ~ v1_funct_2(C_783,'#skF_7',B_782)
      | ~ v1_funct_1(C_783) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_8705])).

tff(c_8768,plain,
    ( k3_funct_2('#skF_7','#skF_8','#skF_9','#skF_5'('#skF_7','#skF_6','#skF_9')) = k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_9'))
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_8722])).

tff(c_8788,plain,(
    k3_funct_2('#skF_7','#skF_8','#skF_9','#skF_5'('#skF_7','#skF_6','#skF_9')) = k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_8768])).

tff(c_8922,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_9')),'#skF_6')
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_6','#skF_9'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_8788,c_78])).

tff(c_8943,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_6','#skF_9')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8703,c_8922])).

tff(c_6273,plain,(
    ! [C_642,B_643] :
      ( ~ r2_hidden(k1_funct_1(C_642,'#skF_5'(k1_relat_1(C_642),B_643,C_642)),B_643)
      | m1_subset_1(C_642,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_642),B_643)))
      | ~ v1_funct_1(C_642)
      | ~ v1_relat_1(C_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_6276,plain,(
    ! [B_643] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_5'('#skF_7',B_643,'#skF_9')),B_643)
      | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_9'),B_643)))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5327,c_6273])).

tff(c_6282,plain,(
    ! [B_643] :
      ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_5'('#skF_7',B_643,'#skF_9')),B_643)
      | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_643))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_84,c_5327,c_6276])).

tff(c_8961,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_8943,c_6282])).

tff(c_9006,plain,(
    v5_relat_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_8961,c_42])).

tff(c_9051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4736,c_9006])).

tff(c_9052,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5325])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [C_109,B_110,A_111] :
      ( v5_relat_1(C_109,B_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_190,plain,(
    ! [C_114,B_115] :
      ( v5_relat_1(C_114,B_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_167])).

tff(c_194,plain,(
    ! [A_9,B_115] :
      ( v5_relat_1(A_9,B_115)
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_190])).

tff(c_4740,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_194,c_4736])).

tff(c_9084,plain,(
    ~ r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9052,c_4740])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9094,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9052,c_9052,c_4])).

tff(c_122,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(A_96,B_97)
      | ~ m1_subset_1(A_96,k1_zfmisc_1(B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_126,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_122])).

tff(c_9178,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9094,c_126])).

tff(c_9181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9084,c_9178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.57/3.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/3.07  
% 8.57/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/3.07  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 8.57/3.07  
% 8.57/3.07  %Foreground sorts:
% 8.57/3.07  
% 8.57/3.07  
% 8.57/3.07  %Background operators:
% 8.57/3.07  
% 8.57/3.07  
% 8.57/3.07  %Foreground operators:
% 8.57/3.07  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.57/3.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.57/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.57/3.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.57/3.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.57/3.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.57/3.07  tff('#skF_7', type, '#skF_7': $i).
% 8.57/3.07  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.57/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.57/3.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.57/3.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.57/3.07  tff('#skF_6', type, '#skF_6': $i).
% 8.57/3.07  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.57/3.07  tff('#skF_9', type, '#skF_9': $i).
% 8.57/3.07  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.57/3.07  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.57/3.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.57/3.07  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.57/3.07  tff('#skF_8', type, '#skF_8': $i).
% 8.57/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.57/3.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.57/3.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.57/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.57/3.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.57/3.07  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.57/3.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.57/3.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.57/3.07  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 8.57/3.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.57/3.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.57/3.07  
% 8.57/3.09  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.57/3.09  tff(f_160, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 8.57/3.09  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.57/3.09  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.57/3.09  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.57/3.09  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.57/3.09  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.57/3.09  tff(f_138, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 8.57/3.09  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.57/3.09  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 8.57/3.09  tff(f_121, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 8.57/3.09  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.57/3.09  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.57/3.09  tff(c_22, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.57/3.09  tff(c_80, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.57/3.09  tff(c_132, plain, (![B_100, A_101]: (v1_relat_1(B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_101)) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.57/3.09  tff(c_138, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_80, c_132])).
% 8.57/3.09  tff(c_142, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_138])).
% 8.57/3.09  tff(c_20, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(B_15), A_14) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.57/3.09  tff(c_4710, plain, (![A_471, B_472, C_473]: (k2_relset_1(A_471, B_472, C_473)=k2_relat_1(C_473) | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(A_471, B_472))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.57/3.09  tff(c_4725, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_4710])).
% 8.57/3.09  tff(c_76, plain, (~r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.57/3.09  tff(c_4726, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4725, c_76])).
% 8.57/3.09  tff(c_4733, plain, (~v5_relat_1('#skF_9', '#skF_6') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_20, c_4726])).
% 8.57/3.09  tff(c_4736, plain, (~v5_relat_1('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_4733])).
% 8.57/3.09  tff(c_84, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.57/3.09  tff(c_82, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.57/3.09  tff(c_4791, plain, (![A_483, B_484, C_485]: (k1_relset_1(A_483, B_484, C_485)=k1_relat_1(C_485) | ~m1_subset_1(C_485, k1_zfmisc_1(k2_zfmisc_1(A_483, B_484))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.57/3.09  tff(c_4811, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_4791])).
% 8.57/3.09  tff(c_5303, plain, (![B_581, A_582, C_583]: (k1_xboole_0=B_581 | k1_relset_1(A_582, B_581, C_583)=A_582 | ~v1_funct_2(C_583, A_582, B_581) | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(A_582, B_581))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.57/3.09  tff(c_5314, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_80, c_5303])).
% 8.57/3.09  tff(c_5325, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4811, c_5314])).
% 8.57/3.09  tff(c_5327, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_5325])).
% 8.57/3.09  tff(c_5977, plain, (![C_632, B_633]: (r2_hidden('#skF_5'(k1_relat_1(C_632), B_633, C_632), k1_relat_1(C_632)) | m1_subset_1(C_632, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_632), B_633))) | ~v1_funct_1(C_632) | ~v1_relat_1(C_632))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.57/3.09  tff(c_5985, plain, (![B_633]: (r2_hidden('#skF_5'('#skF_7', B_633, '#skF_9'), k1_relat_1('#skF_9')) | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_9'), B_633))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5327, c_5977])).
% 8.57/3.09  tff(c_5995, plain, (![B_634]: (r2_hidden('#skF_5'('#skF_7', B_634, '#skF_9'), '#skF_7') | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_634))))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_84, c_5327, c_5327, c_5985])).
% 8.57/3.09  tff(c_42, plain, (![C_60, B_59, A_58]: (v5_relat_1(C_60, B_59) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.57/3.09  tff(c_6039, plain, (![B_635]: (v5_relat_1('#skF_9', B_635) | r2_hidden('#skF_5'('#skF_7', B_635, '#skF_9'), '#skF_7'))), inference(resolution, [status(thm)], [c_5995, c_42])).
% 8.57/3.09  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.57/3.09  tff(c_6050, plain, (![B_635]: (m1_subset_1('#skF_5'('#skF_7', B_635, '#skF_9'), '#skF_7') | v5_relat_1('#skF_9', B_635))), inference(resolution, [status(thm)], [c_6039, c_10])).
% 8.57/3.09  tff(c_88, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.57/3.09  tff(c_6738, plain, (![A_694, B_695, C_696, D_697]: (k3_funct_2(A_694, B_695, C_696, D_697)=k1_funct_1(C_696, D_697) | ~m1_subset_1(D_697, A_694) | ~m1_subset_1(C_696, k1_zfmisc_1(k2_zfmisc_1(A_694, B_695))) | ~v1_funct_2(C_696, A_694, B_695) | ~v1_funct_1(C_696) | v1_xboole_0(A_694))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.57/3.09  tff(c_6750, plain, (![B_695, C_696, B_635]: (k3_funct_2('#skF_7', B_695, C_696, '#skF_5'('#skF_7', B_635, '#skF_9'))=k1_funct_1(C_696, '#skF_5'('#skF_7', B_635, '#skF_9')) | ~m1_subset_1(C_696, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_695))) | ~v1_funct_2(C_696, '#skF_7', B_695) | ~v1_funct_1(C_696) | v1_xboole_0('#skF_7') | v5_relat_1('#skF_9', B_635))), inference(resolution, [status(thm)], [c_6050, c_6738])).
% 8.57/3.09  tff(c_7227, plain, (![B_710, C_711, B_712]: (k3_funct_2('#skF_7', B_710, C_711, '#skF_5'('#skF_7', B_712, '#skF_9'))=k1_funct_1(C_711, '#skF_5'('#skF_7', B_712, '#skF_9')) | ~m1_subset_1(C_711, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_710))) | ~v1_funct_2(C_711, '#skF_7', B_710) | ~v1_funct_1(C_711) | v5_relat_1('#skF_9', B_712))), inference(negUnitSimplification, [status(thm)], [c_88, c_6750])).
% 8.57/3.09  tff(c_7261, plain, (![B_712]: (k3_funct_2('#skF_7', '#skF_8', '#skF_9', '#skF_5'('#skF_7', B_712, '#skF_9'))=k1_funct_1('#skF_9', '#skF_5'('#skF_7', B_712, '#skF_9')) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9') | v5_relat_1('#skF_9', B_712))), inference(resolution, [status(thm)], [c_80, c_7227])).
% 8.57/3.09  tff(c_8449, plain, (![B_773]: (k3_funct_2('#skF_7', '#skF_8', '#skF_9', '#skF_5'('#skF_7', B_773, '#skF_9'))=k1_funct_1('#skF_9', '#skF_5'('#skF_7', B_773, '#skF_9')) | v5_relat_1('#skF_9', B_773))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_7261])).
% 8.57/3.09  tff(c_78, plain, (![E_89]: (r2_hidden(k3_funct_2('#skF_7', '#skF_8', '#skF_9', E_89), '#skF_6') | ~m1_subset_1(E_89, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.57/3.09  tff(c_8651, plain, (![B_778]: (r2_hidden(k1_funct_1('#skF_9', '#skF_5'('#skF_7', B_778, '#skF_9')), '#skF_6') | ~m1_subset_1('#skF_5'('#skF_7', B_778, '#skF_9'), '#skF_7') | v5_relat_1('#skF_9', B_778))), inference(superposition, [status(thm), theory('equality')], [c_8449, c_78])).
% 8.57/3.09  tff(c_5892, plain, (![C_626, B_627]: (~r2_hidden(k1_funct_1(C_626, '#skF_5'(k1_relat_1(C_626), B_627, C_626)), B_627) | v1_funct_2(C_626, k1_relat_1(C_626), B_627) | ~v1_funct_1(C_626) | ~v1_relat_1(C_626))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.57/3.09  tff(c_5895, plain, (![B_627]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_5'('#skF_7', B_627, '#skF_9')), B_627) | v1_funct_2('#skF_9', k1_relat_1('#skF_9'), B_627) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5327, c_5892])).
% 8.57/3.09  tff(c_5901, plain, (![B_627]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_5'('#skF_7', B_627, '#skF_9')), B_627) | v1_funct_2('#skF_9', '#skF_7', B_627))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_84, c_5327, c_5895])).
% 8.57/3.09  tff(c_8659, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_6') | ~m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_9'), '#skF_7') | v5_relat_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_8651, c_5901])).
% 8.57/3.09  tff(c_8670, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_6') | ~m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_9'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_4736, c_8659])).
% 8.57/3.09  tff(c_8673, plain, (~m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_8670])).
% 8.57/3.09  tff(c_8686, plain, (v5_relat_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_6050, c_8673])).
% 8.57/3.09  tff(c_8701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4736, c_8686])).
% 8.57/3.09  tff(c_8703, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_8670])).
% 8.57/3.09  tff(c_62, plain, (![A_70, B_71, C_72, D_73]: (k3_funct_2(A_70, B_71, C_72, D_73)=k1_funct_1(C_72, D_73) | ~m1_subset_1(D_73, A_70) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_2(C_72, A_70, B_71) | ~v1_funct_1(C_72) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.57/3.09  tff(c_8705, plain, (![B_71, C_72]: (k3_funct_2('#skF_7', B_71, C_72, '#skF_5'('#skF_7', '#skF_6', '#skF_9'))=k1_funct_1(C_72, '#skF_5'('#skF_7', '#skF_6', '#skF_9')) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_71))) | ~v1_funct_2(C_72, '#skF_7', B_71) | ~v1_funct_1(C_72) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_8703, c_62])).
% 8.57/3.09  tff(c_8722, plain, (![B_782, C_783]: (k3_funct_2('#skF_7', B_782, C_783, '#skF_5'('#skF_7', '#skF_6', '#skF_9'))=k1_funct_1(C_783, '#skF_5'('#skF_7', '#skF_6', '#skF_9')) | ~m1_subset_1(C_783, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_782))) | ~v1_funct_2(C_783, '#skF_7', B_782) | ~v1_funct_1(C_783))), inference(negUnitSimplification, [status(thm)], [c_88, c_8705])).
% 8.57/3.09  tff(c_8768, plain, (k3_funct_2('#skF_7', '#skF_8', '#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_9'))=k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_9')) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_8722])).
% 8.57/3.09  tff(c_8788, plain, (k3_funct_2('#skF_7', '#skF_8', '#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_9'))=k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_8768])).
% 8.57/3.09  tff(c_8922, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_9')), '#skF_6') | ~m1_subset_1('#skF_5'('#skF_7', '#skF_6', '#skF_9'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_8788, c_78])).
% 8.57/3.09  tff(c_8943, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_6', '#skF_9')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8703, c_8922])).
% 8.57/3.09  tff(c_6273, plain, (![C_642, B_643]: (~r2_hidden(k1_funct_1(C_642, '#skF_5'(k1_relat_1(C_642), B_643, C_642)), B_643) | m1_subset_1(C_642, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_642), B_643))) | ~v1_funct_1(C_642) | ~v1_relat_1(C_642))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.57/3.09  tff(c_6276, plain, (![B_643]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_5'('#skF_7', B_643, '#skF_9')), B_643) | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_9'), B_643))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5327, c_6273])).
% 8.57/3.09  tff(c_6282, plain, (![B_643]: (~r2_hidden(k1_funct_1('#skF_9', '#skF_5'('#skF_7', B_643, '#skF_9')), B_643) | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_643))))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_84, c_5327, c_6276])).
% 8.57/3.09  tff(c_8961, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_8943, c_6282])).
% 8.57/3.09  tff(c_9006, plain, (v5_relat_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_8961, c_42])).
% 8.57/3.09  tff(c_9051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4736, c_9006])).
% 8.57/3.09  tff(c_9052, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_5325])).
% 8.57/3.09  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.57/3.09  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.57/3.09  tff(c_167, plain, (![C_109, B_110, A_111]: (v5_relat_1(C_109, B_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.57/3.09  tff(c_190, plain, (![C_114, B_115]: (v5_relat_1(C_114, B_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_167])).
% 8.57/3.09  tff(c_194, plain, (![A_9, B_115]: (v5_relat_1(A_9, B_115) | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_190])).
% 8.57/3.09  tff(c_4740, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_194, c_4736])).
% 8.57/3.09  tff(c_9084, plain, (~r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9052, c_4740])).
% 8.57/3.09  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.57/3.09  tff(c_9094, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9052, c_9052, c_4])).
% 8.57/3.09  tff(c_122, plain, (![A_96, B_97]: (r1_tarski(A_96, B_97) | ~m1_subset_1(A_96, k1_zfmisc_1(B_97)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.57/3.09  tff(c_126, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_80, c_122])).
% 8.57/3.09  tff(c_9178, plain, (r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9094, c_126])).
% 8.57/3.09  tff(c_9181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9084, c_9178])).
% 8.57/3.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/3.09  
% 8.57/3.09  Inference rules
% 8.57/3.09  ----------------------
% 8.57/3.09  #Ref     : 0
% 8.57/3.09  #Sup     : 2025
% 8.57/3.09  #Fact    : 0
% 8.57/3.09  #Define  : 0
% 8.57/3.09  #Split   : 40
% 8.57/3.09  #Chain   : 0
% 8.57/3.09  #Close   : 0
% 8.57/3.09  
% 8.57/3.09  Ordering : KBO
% 8.57/3.09  
% 8.57/3.09  Simplification rules
% 8.57/3.09  ----------------------
% 8.57/3.09  #Subsume      : 519
% 8.57/3.09  #Demod        : 876
% 8.57/3.09  #Tautology    : 273
% 8.57/3.09  #SimpNegUnit  : 78
% 8.57/3.09  #BackRed      : 150
% 8.57/3.09  
% 8.57/3.09  #Partial instantiations: 0
% 8.57/3.09  #Strategies tried      : 1
% 8.57/3.09  
% 8.57/3.09  Timing (in seconds)
% 8.57/3.09  ----------------------
% 8.57/3.09  Preprocessing        : 0.38
% 8.57/3.09  Parsing              : 0.20
% 8.57/3.09  CNF conversion       : 0.03
% 8.57/3.09  Main loop            : 1.92
% 8.57/3.09  Inferencing          : 0.63
% 8.57/3.09  Reduction            : 0.61
% 8.57/3.09  Demodulation         : 0.40
% 8.57/3.09  BG Simplification    : 0.08
% 8.57/3.09  Subsumption          : 0.42
% 8.57/3.09  Abstraction          : 0.10
% 8.57/3.09  MUC search           : 0.00
% 8.57/3.09  Cooper               : 0.00
% 8.57/3.09  Total                : 2.34
% 8.57/3.09  Index Insertion      : 0.00
% 8.57/3.09  Index Deletion       : 0.00
% 8.57/3.09  Index Matching       : 0.00
% 8.57/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
