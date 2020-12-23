%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:55 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.38s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 385 expanded)
%              Number of leaves         :   41 ( 150 expanded)
%              Depth                    :   14
%              Number of atoms          :  252 (1314 expanded)
%              Number of equality atoms :   47 ( 223 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2508,plain,(
    ! [A_503,B_504,C_505] :
      ( k1_relset_1(A_503,B_504,C_505) = k1_relat_1(C_505)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(A_503,B_504))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2521,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_2508])).

tff(c_36,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2528,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_36])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2602,plain,(
    ! [D_522,B_526,A_527,F_525,E_524,C_523] :
      ( k1_funct_1(k8_funct_2(B_526,C_523,A_527,D_522,E_524),F_525) = k1_funct_1(E_524,k1_funct_1(D_522,F_525))
      | k1_xboole_0 = B_526
      | ~ r1_tarski(k2_relset_1(B_526,C_523,D_522),k1_relset_1(C_523,A_527,E_524))
      | ~ m1_subset_1(F_525,B_526)
      | ~ m1_subset_1(E_524,k1_zfmisc_1(k2_zfmisc_1(C_523,A_527)))
      | ~ v1_funct_1(E_524)
      | ~ m1_subset_1(D_522,k1_zfmisc_1(k2_zfmisc_1(B_526,C_523)))
      | ~ v1_funct_2(D_522,B_526,C_523)
      | ~ v1_funct_1(D_522)
      | v1_xboole_0(C_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2604,plain,(
    ! [B_526,D_522,F_525] :
      ( k1_funct_1(k8_funct_2(B_526,'#skF_3','#skF_1',D_522,'#skF_5'),F_525) = k1_funct_1('#skF_5',k1_funct_1(D_522,F_525))
      | k1_xboole_0 = B_526
      | ~ r1_tarski(k2_relset_1(B_526,'#skF_3',D_522),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_525,B_526)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_522,k1_zfmisc_1(k2_zfmisc_1(B_526,'#skF_3')))
      | ~ v1_funct_2(D_522,B_526,'#skF_3')
      | ~ v1_funct_1(D_522)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2521,c_2602])).

tff(c_2606,plain,(
    ! [B_526,D_522,F_525] :
      ( k1_funct_1(k8_funct_2(B_526,'#skF_3','#skF_1',D_522,'#skF_5'),F_525) = k1_funct_1('#skF_5',k1_funct_1(D_522,F_525))
      | k1_xboole_0 = B_526
      | ~ r1_tarski(k2_relset_1(B_526,'#skF_3',D_522),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_525,B_526)
      | ~ m1_subset_1(D_522,k1_zfmisc_1(k2_zfmisc_1(B_526,'#skF_3')))
      | ~ v1_funct_2(D_522,B_526,'#skF_3')
      | ~ v1_funct_1(D_522)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2604])).

tff(c_2628,plain,(
    ! [B_535,D_536,F_537] :
      ( k1_funct_1(k8_funct_2(B_535,'#skF_3','#skF_1',D_536,'#skF_5'),F_537) = k1_funct_1('#skF_5',k1_funct_1(D_536,F_537))
      | k1_xboole_0 = B_535
      | ~ r1_tarski(k2_relset_1(B_535,'#skF_3',D_536),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_537,B_535)
      | ~ m1_subset_1(D_536,k1_zfmisc_1(k2_zfmisc_1(B_535,'#skF_3')))
      | ~ v1_funct_2(D_536,B_535,'#skF_3')
      | ~ v1_funct_1(D_536) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2606])).

tff(c_2630,plain,(
    ! [F_537] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_537) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_537))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_537,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2528,c_2628])).

tff(c_2633,plain,(
    ! [F_537] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_537) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_537))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_537,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_2630])).

tff(c_2634,plain,(
    ! [F_537] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_537) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_537))
      | ~ m1_subset_1(F_537,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2633])).

tff(c_2566,plain,(
    ! [D_514,C_515,A_516,B_517] :
      ( r2_hidden(k1_funct_1(D_514,C_515),k2_relset_1(A_516,B_517,D_514))
      | k1_xboole_0 = B_517
      | ~ r2_hidden(C_515,A_516)
      | ~ m1_subset_1(D_514,k1_zfmisc_1(k2_zfmisc_1(A_516,B_517)))
      | ~ v1_funct_2(D_514,A_516,B_517)
      | ~ v1_funct_1(D_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_162,plain,(
    ! [A_87,C_88,B_89] :
      ( m1_subset_1(A_87,C_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(C_88))
      | ~ r2_hidden(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_169,plain,(
    ! [A_87,B_5,A_4] :
      ( m1_subset_1(A_87,B_5)
      | ~ r2_hidden(A_87,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_162])).

tff(c_2647,plain,(
    ! [B_541,A_539,C_540,B_543,D_542] :
      ( m1_subset_1(k1_funct_1(D_542,C_540),B_541)
      | ~ r1_tarski(k2_relset_1(A_539,B_543,D_542),B_541)
      | k1_xboole_0 = B_543
      | ~ r2_hidden(C_540,A_539)
      | ~ m1_subset_1(D_542,k1_zfmisc_1(k2_zfmisc_1(A_539,B_543)))
      | ~ v1_funct_2(D_542,A_539,B_543)
      | ~ v1_funct_1(D_542) ) ),
    inference(resolution,[status(thm)],[c_2566,c_169])).

tff(c_2649,plain,(
    ! [C_540] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_540),k1_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_540,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2528,c_2647])).

tff(c_2652,plain,(
    ! [C_540] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_540),k1_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_540,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_2649])).

tff(c_2653,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2652])).

tff(c_2663,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2653,c_2])).

tff(c_2666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2663])).

tff(c_2669,plain,(
    ! [C_544] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_544),k1_relat_1('#skF_5'))
      | ~ r2_hidden(C_544,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_2652])).

tff(c_132,plain,(
    ! [C_78,B_79,A_80] :
      ( ~ v1_xboole_0(C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_144,plain,(
    ! [B_81,A_82,A_83] :
      ( ~ v1_xboole_0(B_81)
      | ~ r2_hidden(A_82,A_83)
      | ~ r1_tarski(A_83,B_81) ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_190,plain,(
    ! [B_98,B_99,A_100] :
      ( ~ v1_xboole_0(B_98)
      | ~ r1_tarski(B_99,B_98)
      | v1_xboole_0(B_99)
      | ~ m1_subset_1(A_100,B_99) ) ),
    inference(resolution,[status(thm)],[c_6,c_144])).

tff(c_197,plain,(
    ! [A_100] :
      ( ~ v1_xboole_0(k1_relset_1('#skF_3','#skF_1','#skF_5'))
      | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(A_100,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_190])).

tff(c_1510,plain,(
    ~ v1_xboole_0(k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_2526,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_1510])).

tff(c_18,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_81,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_88,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_81])).

tff(c_107,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_120,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_2548,plain,(
    ! [A_507,B_508,C_509] :
      ( k7_partfun1(A_507,B_508,C_509) = k1_funct_1(B_508,C_509)
      | ~ r2_hidden(C_509,k1_relat_1(B_508))
      | ~ v1_funct_1(B_508)
      | ~ v5_relat_1(B_508,A_507)
      | ~ v1_relat_1(B_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2573,plain,(
    ! [A_518,B_519,A_520] :
      ( k7_partfun1(A_518,B_519,A_520) = k1_funct_1(B_519,A_520)
      | ~ v1_funct_1(B_519)
      | ~ v5_relat_1(B_519,A_518)
      | ~ v1_relat_1(B_519)
      | v1_xboole_0(k1_relat_1(B_519))
      | ~ m1_subset_1(A_520,k1_relat_1(B_519)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2548])).

tff(c_2575,plain,(
    ! [A_520] :
      ( k7_partfun1('#skF_1','#skF_5',A_520) = k1_funct_1('#skF_5',A_520)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_520,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_120,c_2573])).

tff(c_2580,plain,(
    ! [A_520] :
      ( k7_partfun1('#skF_1','#skF_5',A_520) = k1_funct_1('#skF_5',A_520)
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_520,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_42,c_2575])).

tff(c_2581,plain,(
    ! [A_520] :
      ( k7_partfun1('#skF_1','#skF_5',A_520) = k1_funct_1('#skF_5',A_520)
      | ~ m1_subset_1(A_520,k1_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2526,c_2580])).

tff(c_2674,plain,(
    ! [C_545] :
      ( k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4',C_545)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_545))
      | ~ r2_hidden(C_545,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2669,c_2581])).

tff(c_32,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2680,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2674,c_32])).

tff(c_2686,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2680])).

tff(c_2689,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2686])).

tff(c_2692,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2689])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2696,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2692,c_4])).

tff(c_2700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2696])).

tff(c_2701,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2680])).

tff(c_2713,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2634,c_2701])).

tff(c_2717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2713])).

tff(c_2719,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_2737,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2719,c_4])).

tff(c_2740,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_36])).

tff(c_3004,plain,(
    ! [D_593,C_594,A_595,B_596] :
      ( r2_hidden(k1_funct_1(D_593,C_594),k2_relset_1(A_595,B_596,D_593))
      | k1_xboole_0 = B_596
      | ~ r2_hidden(C_594,A_595)
      | ~ m1_subset_1(D_593,k1_zfmisc_1(k2_zfmisc_1(A_595,B_596)))
      | ~ v1_funct_2(D_593,A_595,B_596)
      | ~ v1_funct_1(D_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_139,plain,(
    ! [B_5,A_80,A_4] :
      ( ~ v1_xboole_0(B_5)
      | ~ r2_hidden(A_80,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_3017,plain,(
    ! [B_601,C_600,D_599,A_602,B_603] :
      ( ~ v1_xboole_0(B_601)
      | ~ r1_tarski(k2_relset_1(A_602,B_603,D_599),B_601)
      | k1_xboole_0 = B_603
      | ~ r2_hidden(C_600,A_602)
      | ~ m1_subset_1(D_599,k1_zfmisc_1(k2_zfmisc_1(A_602,B_603)))
      | ~ v1_funct_2(D_599,A_602,B_603)
      | ~ v1_funct_1(D_599) ) ),
    inference(resolution,[status(thm)],[c_3004,c_139])).

tff(c_3019,plain,(
    ! [C_600] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_600,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2740,c_3017])).

tff(c_3022,plain,(
    ! [C_600] :
      ( k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_600,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_2,c_3019])).

tff(c_3024,plain,(
    ! [C_604] : ~ r2_hidden(C_604,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3022])).

tff(c_3029,plain,(
    ! [A_2] :
      ( v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_3024])).

tff(c_3030,plain,(
    ! [A_2] : ~ m1_subset_1(A_2,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3029])).

tff(c_3032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3030,c_38])).

tff(c_3033,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3029])).

tff(c_3036,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3033,c_4])).

tff(c_3040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3036])).

tff(c_3041,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3022])).

tff(c_3053,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3041,c_2])).

tff(c_3056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:33:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.38/1.98  
% 5.38/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.38/1.98  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.38/1.98  
% 5.38/1.98  %Foreground sorts:
% 5.38/1.98  
% 5.38/1.98  
% 5.38/1.98  %Background operators:
% 5.38/1.98  
% 5.38/1.98  
% 5.38/1.98  %Foreground operators:
% 5.38/1.98  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.38/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.38/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.38/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.38/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.38/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.38/1.98  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 5.38/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.38/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.38/1.98  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 5.38/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.38/1.98  tff('#skF_2', type, '#skF_2': $i).
% 5.38/1.98  tff('#skF_3', type, '#skF_3': $i).
% 5.38/1.98  tff('#skF_1', type, '#skF_1': $i).
% 5.38/1.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.38/1.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.38/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.38/1.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.38/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.38/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.38/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.38/1.98  tff('#skF_4', type, '#skF_4': $i).
% 5.38/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.38/1.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.38/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.38/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.38/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.38/1.98  
% 5.38/2.00  tff(f_144, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 5.38/2.00  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.38/2.00  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.38/2.00  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.38/2.00  tff(f_107, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 5.38/2.00  tff(f_119, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 5.38/2.00  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.38/2.00  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.38/2.00  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.38/2.00  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.38/2.00  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.38/2.00  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.38/2.00  tff(f_83, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 5.38/2.00  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.38/2.00  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.38/2.00  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.38/2.00  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.38/2.00  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.38/2.00  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.38/2.00  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.38/2.00  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.38/2.00  tff(c_38, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.38/2.00  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.38/2.00  tff(c_2508, plain, (![A_503, B_504, C_505]: (k1_relset_1(A_503, B_504, C_505)=k1_relat_1(C_505) | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(A_503, B_504))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.38/2.00  tff(c_2521, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_2508])).
% 5.38/2.00  tff(c_36, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.38/2.00  tff(c_2528, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2521, c_36])).
% 5.38/2.00  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.38/2.00  tff(c_2602, plain, (![D_522, B_526, A_527, F_525, E_524, C_523]: (k1_funct_1(k8_funct_2(B_526, C_523, A_527, D_522, E_524), F_525)=k1_funct_1(E_524, k1_funct_1(D_522, F_525)) | k1_xboole_0=B_526 | ~r1_tarski(k2_relset_1(B_526, C_523, D_522), k1_relset_1(C_523, A_527, E_524)) | ~m1_subset_1(F_525, B_526) | ~m1_subset_1(E_524, k1_zfmisc_1(k2_zfmisc_1(C_523, A_527))) | ~v1_funct_1(E_524) | ~m1_subset_1(D_522, k1_zfmisc_1(k2_zfmisc_1(B_526, C_523))) | ~v1_funct_2(D_522, B_526, C_523) | ~v1_funct_1(D_522) | v1_xboole_0(C_523))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.38/2.00  tff(c_2604, plain, (![B_526, D_522, F_525]: (k1_funct_1(k8_funct_2(B_526, '#skF_3', '#skF_1', D_522, '#skF_5'), F_525)=k1_funct_1('#skF_5', k1_funct_1(D_522, F_525)) | k1_xboole_0=B_526 | ~r1_tarski(k2_relset_1(B_526, '#skF_3', D_522), k1_relat_1('#skF_5')) | ~m1_subset_1(F_525, B_526) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_522, k1_zfmisc_1(k2_zfmisc_1(B_526, '#skF_3'))) | ~v1_funct_2(D_522, B_526, '#skF_3') | ~v1_funct_1(D_522) | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2521, c_2602])).
% 5.38/2.00  tff(c_2606, plain, (![B_526, D_522, F_525]: (k1_funct_1(k8_funct_2(B_526, '#skF_3', '#skF_1', D_522, '#skF_5'), F_525)=k1_funct_1('#skF_5', k1_funct_1(D_522, F_525)) | k1_xboole_0=B_526 | ~r1_tarski(k2_relset_1(B_526, '#skF_3', D_522), k1_relat_1('#skF_5')) | ~m1_subset_1(F_525, B_526) | ~m1_subset_1(D_522, k1_zfmisc_1(k2_zfmisc_1(B_526, '#skF_3'))) | ~v1_funct_2(D_522, B_526, '#skF_3') | ~v1_funct_1(D_522) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2604])).
% 5.38/2.00  tff(c_2628, plain, (![B_535, D_536, F_537]: (k1_funct_1(k8_funct_2(B_535, '#skF_3', '#skF_1', D_536, '#skF_5'), F_537)=k1_funct_1('#skF_5', k1_funct_1(D_536, F_537)) | k1_xboole_0=B_535 | ~r1_tarski(k2_relset_1(B_535, '#skF_3', D_536), k1_relat_1('#skF_5')) | ~m1_subset_1(F_537, B_535) | ~m1_subset_1(D_536, k1_zfmisc_1(k2_zfmisc_1(B_535, '#skF_3'))) | ~v1_funct_2(D_536, B_535, '#skF_3') | ~v1_funct_1(D_536))), inference(negUnitSimplification, [status(thm)], [c_50, c_2606])).
% 5.38/2.00  tff(c_2630, plain, (![F_537]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_537)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_537)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_537, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2528, c_2628])).
% 5.38/2.00  tff(c_2633, plain, (![F_537]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_537)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_537)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_537, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_2630])).
% 5.38/2.00  tff(c_2634, plain, (![F_537]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_537)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_537)) | ~m1_subset_1(F_537, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_2633])).
% 5.38/2.00  tff(c_2566, plain, (![D_514, C_515, A_516, B_517]: (r2_hidden(k1_funct_1(D_514, C_515), k2_relset_1(A_516, B_517, D_514)) | k1_xboole_0=B_517 | ~r2_hidden(C_515, A_516) | ~m1_subset_1(D_514, k1_zfmisc_1(k2_zfmisc_1(A_516, B_517))) | ~v1_funct_2(D_514, A_516, B_517) | ~v1_funct_1(D_514))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.38/2.00  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.38/2.00  tff(c_162, plain, (![A_87, C_88, B_89]: (m1_subset_1(A_87, C_88) | ~m1_subset_1(B_89, k1_zfmisc_1(C_88)) | ~r2_hidden(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.38/2.00  tff(c_169, plain, (![A_87, B_5, A_4]: (m1_subset_1(A_87, B_5) | ~r2_hidden(A_87, A_4) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_10, c_162])).
% 5.38/2.00  tff(c_2647, plain, (![B_541, A_539, C_540, B_543, D_542]: (m1_subset_1(k1_funct_1(D_542, C_540), B_541) | ~r1_tarski(k2_relset_1(A_539, B_543, D_542), B_541) | k1_xboole_0=B_543 | ~r2_hidden(C_540, A_539) | ~m1_subset_1(D_542, k1_zfmisc_1(k2_zfmisc_1(A_539, B_543))) | ~v1_funct_2(D_542, A_539, B_543) | ~v1_funct_1(D_542))), inference(resolution, [status(thm)], [c_2566, c_169])).
% 5.38/2.00  tff(c_2649, plain, (![C_540]: (m1_subset_1(k1_funct_1('#skF_4', C_540), k1_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_540, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2528, c_2647])).
% 5.38/2.00  tff(c_2652, plain, (![C_540]: (m1_subset_1(k1_funct_1('#skF_4', C_540), k1_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_540, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_2649])).
% 5.38/2.00  tff(c_2653, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2652])).
% 5.38/2.00  tff(c_2663, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2653, c_2])).
% 5.38/2.00  tff(c_2666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_2663])).
% 5.38/2.00  tff(c_2669, plain, (![C_544]: (m1_subset_1(k1_funct_1('#skF_4', C_544), k1_relat_1('#skF_5')) | ~r2_hidden(C_544, '#skF_2'))), inference(splitRight, [status(thm)], [c_2652])).
% 5.38/2.00  tff(c_132, plain, (![C_78, B_79, A_80]: (~v1_xboole_0(C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.38/2.00  tff(c_144, plain, (![B_81, A_82, A_83]: (~v1_xboole_0(B_81) | ~r2_hidden(A_82, A_83) | ~r1_tarski(A_83, B_81))), inference(resolution, [status(thm)], [c_10, c_132])).
% 5.38/2.00  tff(c_190, plain, (![B_98, B_99, A_100]: (~v1_xboole_0(B_98) | ~r1_tarski(B_99, B_98) | v1_xboole_0(B_99) | ~m1_subset_1(A_100, B_99))), inference(resolution, [status(thm)], [c_6, c_144])).
% 5.38/2.00  tff(c_197, plain, (![A_100]: (~v1_xboole_0(k1_relset_1('#skF_3', '#skF_1', '#skF_5')) | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(A_100, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_36, c_190])).
% 5.38/2.00  tff(c_1510, plain, (~v1_xboole_0(k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(splitLeft, [status(thm)], [c_197])).
% 5.38/2.00  tff(c_2526, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2521, c_1510])).
% 5.38/2.00  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.38/2.00  tff(c_72, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.38/2.00  tff(c_81, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_40, c_72])).
% 5.38/2.00  tff(c_88, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_81])).
% 5.38/2.00  tff(c_107, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.38/2.00  tff(c_120, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_107])).
% 5.38/2.00  tff(c_2548, plain, (![A_507, B_508, C_509]: (k7_partfun1(A_507, B_508, C_509)=k1_funct_1(B_508, C_509) | ~r2_hidden(C_509, k1_relat_1(B_508)) | ~v1_funct_1(B_508) | ~v5_relat_1(B_508, A_507) | ~v1_relat_1(B_508))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.38/2.00  tff(c_2573, plain, (![A_518, B_519, A_520]: (k7_partfun1(A_518, B_519, A_520)=k1_funct_1(B_519, A_520) | ~v1_funct_1(B_519) | ~v5_relat_1(B_519, A_518) | ~v1_relat_1(B_519) | v1_xboole_0(k1_relat_1(B_519)) | ~m1_subset_1(A_520, k1_relat_1(B_519)))), inference(resolution, [status(thm)], [c_6, c_2548])).
% 5.38/2.00  tff(c_2575, plain, (![A_520]: (k7_partfun1('#skF_1', '#skF_5', A_520)=k1_funct_1('#skF_5', A_520) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_520, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_120, c_2573])).
% 5.38/2.00  tff(c_2580, plain, (![A_520]: (k7_partfun1('#skF_1', '#skF_5', A_520)=k1_funct_1('#skF_5', A_520) | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_520, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_42, c_2575])).
% 5.38/2.00  tff(c_2581, plain, (![A_520]: (k7_partfun1('#skF_1', '#skF_5', A_520)=k1_funct_1('#skF_5', A_520) | ~m1_subset_1(A_520, k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2526, c_2580])).
% 5.38/2.00  tff(c_2674, plain, (![C_545]: (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', C_545))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_545)) | ~r2_hidden(C_545, '#skF_2'))), inference(resolution, [status(thm)], [c_2669, c_2581])).
% 5.38/2.00  tff(c_32, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.38/2.00  tff(c_2680, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2674, c_32])).
% 5.38/2.00  tff(c_2686, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(splitLeft, [status(thm)], [c_2680])).
% 5.38/2.00  tff(c_2689, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_2686])).
% 5.38/2.00  tff(c_2692, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2689])).
% 5.38/2.00  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.38/2.00  tff(c_2696, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2692, c_4])).
% 5.38/2.00  tff(c_2700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2696])).
% 5.38/2.00  tff(c_2701, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_2680])).
% 5.38/2.00  tff(c_2713, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2634, c_2701])).
% 5.38/2.00  tff(c_2717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_2713])).
% 5.38/2.00  tff(c_2719, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(splitRight, [status(thm)], [c_197])).
% 5.38/2.00  tff(c_2737, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2719, c_4])).
% 5.38/2.00  tff(c_2740, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_36])).
% 5.38/2.00  tff(c_3004, plain, (![D_593, C_594, A_595, B_596]: (r2_hidden(k1_funct_1(D_593, C_594), k2_relset_1(A_595, B_596, D_593)) | k1_xboole_0=B_596 | ~r2_hidden(C_594, A_595) | ~m1_subset_1(D_593, k1_zfmisc_1(k2_zfmisc_1(A_595, B_596))) | ~v1_funct_2(D_593, A_595, B_596) | ~v1_funct_1(D_593))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.38/2.00  tff(c_139, plain, (![B_5, A_80, A_4]: (~v1_xboole_0(B_5) | ~r2_hidden(A_80, A_4) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_10, c_132])).
% 5.38/2.00  tff(c_3017, plain, (![B_601, C_600, D_599, A_602, B_603]: (~v1_xboole_0(B_601) | ~r1_tarski(k2_relset_1(A_602, B_603, D_599), B_601) | k1_xboole_0=B_603 | ~r2_hidden(C_600, A_602) | ~m1_subset_1(D_599, k1_zfmisc_1(k2_zfmisc_1(A_602, B_603))) | ~v1_funct_2(D_599, A_602, B_603) | ~v1_funct_1(D_599))), inference(resolution, [status(thm)], [c_3004, c_139])).
% 5.38/2.00  tff(c_3019, plain, (![C_600]: (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_3' | ~r2_hidden(C_600, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2740, c_3017])).
% 5.38/2.00  tff(c_3022, plain, (![C_600]: (k1_xboole_0='#skF_3' | ~r2_hidden(C_600, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_2, c_3019])).
% 5.38/2.00  tff(c_3024, plain, (![C_604]: (~r2_hidden(C_604, '#skF_2'))), inference(splitLeft, [status(thm)], [c_3022])).
% 5.38/2.00  tff(c_3029, plain, (![A_2]: (v1_xboole_0('#skF_2') | ~m1_subset_1(A_2, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_3024])).
% 5.38/2.00  tff(c_3030, plain, (![A_2]: (~m1_subset_1(A_2, '#skF_2'))), inference(splitLeft, [status(thm)], [c_3029])).
% 5.38/2.00  tff(c_3032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3030, c_38])).
% 5.38/2.00  tff(c_3033, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_3029])).
% 5.38/2.00  tff(c_3036, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3033, c_4])).
% 5.38/2.00  tff(c_3040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_3036])).
% 5.38/2.00  tff(c_3041, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3022])).
% 5.38/2.00  tff(c_3053, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3041, c_2])).
% 5.38/2.00  tff(c_3056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_3053])).
% 5.38/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.38/2.00  
% 5.38/2.00  Inference rules
% 5.38/2.00  ----------------------
% 5.38/2.00  #Ref     : 0
% 5.38/2.00  #Sup     : 552
% 5.38/2.00  #Fact    : 0
% 5.38/2.00  #Define  : 0
% 5.38/2.00  #Split   : 70
% 5.38/2.00  #Chain   : 0
% 5.38/2.00  #Close   : 0
% 5.38/2.00  
% 5.38/2.00  Ordering : KBO
% 5.38/2.00  
% 5.38/2.00  Simplification rules
% 5.38/2.00  ----------------------
% 5.38/2.00  #Subsume      : 114
% 5.38/2.00  #Demod        : 668
% 5.38/2.00  #Tautology    : 185
% 5.38/2.00  #SimpNegUnit  : 90
% 5.38/2.00  #BackRed      : 243
% 5.38/2.00  
% 5.38/2.00  #Partial instantiations: 0
% 5.38/2.00  #Strategies tried      : 1
% 5.38/2.00  
% 5.38/2.00  Timing (in seconds)
% 5.38/2.00  ----------------------
% 5.38/2.01  Preprocessing        : 0.33
% 5.38/2.01  Parsing              : 0.17
% 5.38/2.01  CNF conversion       : 0.03
% 5.38/2.01  Main loop            : 0.88
% 5.38/2.01  Inferencing          : 0.31
% 5.38/2.01  Reduction            : 0.28
% 5.38/2.01  Demodulation         : 0.19
% 5.38/2.01  BG Simplification    : 0.04
% 5.38/2.01  Subsumption          : 0.17
% 5.38/2.01  Abstraction          : 0.04
% 5.38/2.01  MUC search           : 0.00
% 5.38/2.01  Cooper               : 0.00
% 5.38/2.01  Total                : 1.24
% 5.38/2.01  Index Insertion      : 0.00
% 5.38/2.01  Index Deletion       : 0.00
% 5.38/2.01  Index Matching       : 0.00
% 5.38/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
