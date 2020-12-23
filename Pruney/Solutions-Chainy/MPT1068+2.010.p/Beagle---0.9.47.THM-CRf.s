%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:42 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 180 expanded)
%              Number of leaves         :   38 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  163 ( 692 expanded)
%              Number of equality atoms :   36 ( 144 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_relat_1(E)
            & v1_funct_1(E) )
         => ( r2_hidden(C,A)
           => ( B = k1_xboole_0
              | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_42,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_131,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_152,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_131])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_276,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_xboole_0(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_303,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_276])).

tff(c_309,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_365,plain,(
    ! [D_104,F_108,C_109,A_107,E_106,B_105] :
      ( k1_partfun1(A_107,B_105,C_109,D_104,E_106,F_108) = k5_relat_1(E_106,F_108)
      | ~ m1_subset_1(F_108,k1_zfmisc_1(k2_zfmisc_1(C_109,D_104)))
      | ~ v1_funct_1(F_108)
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_105)))
      | ~ v1_funct_1(E_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_377,plain,(
    ! [A_107,B_105,E_106] :
      ( k1_partfun1(A_107,B_105,'#skF_4','#skF_2',E_106,'#skF_6') = k5_relat_1(E_106,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_105)))
      | ~ v1_funct_1(E_106) ) ),
    inference(resolution,[status(thm)],[c_44,c_365])).

tff(c_19806,plain,(
    ! [A_2640,B_2641,E_2642] :
      ( k1_partfun1(A_2640,B_2641,'#skF_4','#skF_2',E_2642,'#skF_6') = k5_relat_1(E_2642,'#skF_6')
      | ~ m1_subset_1(E_2642,k1_zfmisc_1(k2_zfmisc_1(A_2640,B_2641)))
      | ~ v1_funct_1(E_2642) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_377])).

tff(c_19817,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_19806])).

tff(c_19835,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_19817])).

tff(c_40,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_19861,plain,(
    ! [B_2647,C_2646,A_2645,E_2648,D_2644] :
      ( k1_partfun1(A_2645,B_2647,B_2647,C_2646,D_2644,E_2648) = k8_funct_2(A_2645,B_2647,C_2646,D_2644,E_2648)
      | k1_xboole_0 = B_2647
      | ~ r1_tarski(k2_relset_1(A_2645,B_2647,D_2644),k1_relset_1(B_2647,C_2646,E_2648))
      | ~ m1_subset_1(E_2648,k1_zfmisc_1(k2_zfmisc_1(B_2647,C_2646)))
      | ~ v1_funct_1(E_2648)
      | ~ m1_subset_1(D_2644,k1_zfmisc_1(k2_zfmisc_1(A_2645,B_2647)))
      | ~ v1_funct_2(D_2644,A_2645,B_2647)
      | ~ v1_funct_1(D_2644) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_19864,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_19861])).

tff(c_19867,plain,
    ( k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_19835,c_19864])).

tff(c_19868,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_19867])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_102,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_14,c_90])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [B_61,A_62] :
      ( ~ r1_tarski(B_61,A_62)
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_104,plain,(
    ! [A_66] :
      ( ~ r1_tarski(A_66,'#skF_1'(A_66))
      | v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_109,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_102,c_104])).

tff(c_19882,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19868,c_109])).

tff(c_19890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_19882])).

tff(c_19892,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_19867])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_19778,plain,(
    ! [D_2632,C_2634,A_2630,E_2633,B_2631] :
      ( k1_funct_1(k5_relat_1(D_2632,E_2633),C_2634) = k1_funct_1(E_2633,k1_funct_1(D_2632,C_2634))
      | k1_xboole_0 = B_2631
      | ~ r2_hidden(C_2634,A_2630)
      | ~ v1_funct_1(E_2633)
      | ~ v1_relat_1(E_2633)
      | ~ m1_subset_1(D_2632,k1_zfmisc_1(k2_zfmisc_1(A_2630,B_2631)))
      | ~ v1_funct_2(D_2632,A_2630,B_2631)
      | ~ v1_funct_1(D_2632) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_20754,plain,(
    ! [B_2743,E_2742,D_2744,A_2745,B_2741] :
      ( k1_funct_1(k5_relat_1(D_2744,E_2742),A_2745) = k1_funct_1(E_2742,k1_funct_1(D_2744,A_2745))
      | k1_xboole_0 = B_2741
      | ~ v1_funct_1(E_2742)
      | ~ v1_relat_1(E_2742)
      | ~ m1_subset_1(D_2744,k1_zfmisc_1(k2_zfmisc_1(B_2743,B_2741)))
      | ~ v1_funct_2(D_2744,B_2743,B_2741)
      | ~ v1_funct_1(D_2744)
      | v1_xboole_0(B_2743)
      | ~ m1_subset_1(A_2745,B_2743) ) ),
    inference(resolution,[status(thm)],[c_16,c_19778])).

tff(c_20768,plain,(
    ! [E_2742,A_2745] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_2742),A_2745) = k1_funct_1(E_2742,k1_funct_1('#skF_5',A_2745))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_2742)
      | ~ v1_relat_1(E_2742)
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_2745,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_20754])).

tff(c_20784,plain,(
    ! [E_2742,A_2745] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_2742),A_2745) = k1_funct_1(E_2742,k1_funct_1('#skF_5',A_2745))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_2742)
      | ~ v1_relat_1(E_2742)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_2745,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_20768])).

tff(c_20793,plain,(
    ! [E_2746,A_2747] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_2746),A_2747) = k1_funct_1(E_2746,k1_funct_1('#skF_5',A_2747))
      | ~ v1_funct_1(E_2746)
      | ~ v1_relat_1(E_2746)
      | ~ m1_subset_1(A_2747,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_19892,c_20784])).

tff(c_19891,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_19867])).

tff(c_36,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_19927,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19891,c_36])).

tff(c_20803,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20793,c_19927])).

tff(c_20815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_152,c_46,c_20803])).

tff(c_20817,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20824,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20817,c_6])).

tff(c_20828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_20824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:40:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.41/4.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/4.93  
% 11.41/4.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/4.94  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 11.41/4.94  
% 11.41/4.94  %Foreground sorts:
% 11.41/4.94  
% 11.41/4.94  
% 11.41/4.94  %Background operators:
% 11.41/4.94  
% 11.41/4.94  
% 11.41/4.94  %Foreground operators:
% 11.41/4.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.41/4.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.41/4.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.41/4.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.41/4.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.41/4.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.41/4.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.41/4.94  tff('#skF_7', type, '#skF_7': $i).
% 11.41/4.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.41/4.94  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.41/4.94  tff('#skF_5', type, '#skF_5': $i).
% 11.41/4.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.41/4.94  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 11.41/4.94  tff('#skF_6', type, '#skF_6': $i).
% 11.41/4.94  tff('#skF_2', type, '#skF_2': $i).
% 11.41/4.94  tff('#skF_3', type, '#skF_3': $i).
% 11.41/4.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.41/4.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.41/4.94  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.41/4.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.41/4.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.41/4.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.41/4.94  tff('#skF_4', type, '#skF_4': $i).
% 11.41/4.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.41/4.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.41/4.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.41/4.94  
% 11.41/4.95  tff(f_144, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 11.41/4.95  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.41/4.95  tff(f_75, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 11.41/4.95  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.41/4.95  tff(f_92, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 11.41/4.95  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 11.41/4.95  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.41/4.95  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.41/4.95  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.41/4.95  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 11.41/4.95  tff(f_119, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 11.41/4.95  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.41/4.95  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.41/4.95  tff(c_42, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.41/4.95  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.41/4.95  tff(c_131, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.41/4.95  tff(c_152, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_131])).
% 11.41/4.95  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.41/4.95  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.41/4.95  tff(c_276, plain, (![C_95, A_96, B_97]: (v1_xboole_0(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.41/4.95  tff(c_303, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_276])).
% 11.41/4.95  tff(c_309, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_303])).
% 11.41/4.95  tff(c_54, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.41/4.95  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.41/4.95  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.41/4.95  tff(c_365, plain, (![D_104, F_108, C_109, A_107, E_106, B_105]: (k1_partfun1(A_107, B_105, C_109, D_104, E_106, F_108)=k5_relat_1(E_106, F_108) | ~m1_subset_1(F_108, k1_zfmisc_1(k2_zfmisc_1(C_109, D_104))) | ~v1_funct_1(F_108) | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_105))) | ~v1_funct_1(E_106))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.41/4.95  tff(c_377, plain, (![A_107, B_105, E_106]: (k1_partfun1(A_107, B_105, '#skF_4', '#skF_2', E_106, '#skF_6')=k5_relat_1(E_106, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_105))) | ~v1_funct_1(E_106))), inference(resolution, [status(thm)], [c_44, c_365])).
% 11.41/4.95  tff(c_19806, plain, (![A_2640, B_2641, E_2642]: (k1_partfun1(A_2640, B_2641, '#skF_4', '#skF_2', E_2642, '#skF_6')=k5_relat_1(E_2642, '#skF_6') | ~m1_subset_1(E_2642, k1_zfmisc_1(k2_zfmisc_1(A_2640, B_2641))) | ~v1_funct_1(E_2642))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_377])).
% 11.41/4.95  tff(c_19817, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_19806])).
% 11.41/4.95  tff(c_19835, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_19817])).
% 11.41/4.95  tff(c_40, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.41/4.95  tff(c_19861, plain, (![B_2647, C_2646, A_2645, E_2648, D_2644]: (k1_partfun1(A_2645, B_2647, B_2647, C_2646, D_2644, E_2648)=k8_funct_2(A_2645, B_2647, C_2646, D_2644, E_2648) | k1_xboole_0=B_2647 | ~r1_tarski(k2_relset_1(A_2645, B_2647, D_2644), k1_relset_1(B_2647, C_2646, E_2648)) | ~m1_subset_1(E_2648, k1_zfmisc_1(k2_zfmisc_1(B_2647, C_2646))) | ~v1_funct_1(E_2648) | ~m1_subset_1(D_2644, k1_zfmisc_1(k2_zfmisc_1(A_2645, B_2647))) | ~v1_funct_2(D_2644, A_2645, B_2647) | ~v1_funct_1(D_2644))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.41/4.95  tff(c_19864, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_19861])).
% 11.41/4.95  tff(c_19867, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_19835, c_19864])).
% 11.41/4.95  tff(c_19868, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_19867])).
% 11.41/4.95  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.41/4.95  tff(c_90, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.41/4.95  tff(c_102, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_14, c_90])).
% 11.41/4.95  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.41/4.95  tff(c_85, plain, (![B_61, A_62]: (~r1_tarski(B_61, A_62) | ~r2_hidden(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.41/4.95  tff(c_104, plain, (![A_66]: (~r1_tarski(A_66, '#skF_1'(A_66)) | v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_4, c_85])).
% 11.41/4.95  tff(c_109, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_102, c_104])).
% 11.41/4.95  tff(c_19882, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19868, c_109])).
% 11.41/4.95  tff(c_19890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_19882])).
% 11.41/4.95  tff(c_19892, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_19867])).
% 11.41/4.95  tff(c_16, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.41/4.95  tff(c_19778, plain, (![D_2632, C_2634, A_2630, E_2633, B_2631]: (k1_funct_1(k5_relat_1(D_2632, E_2633), C_2634)=k1_funct_1(E_2633, k1_funct_1(D_2632, C_2634)) | k1_xboole_0=B_2631 | ~r2_hidden(C_2634, A_2630) | ~v1_funct_1(E_2633) | ~v1_relat_1(E_2633) | ~m1_subset_1(D_2632, k1_zfmisc_1(k2_zfmisc_1(A_2630, B_2631))) | ~v1_funct_2(D_2632, A_2630, B_2631) | ~v1_funct_1(D_2632))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.41/4.95  tff(c_20754, plain, (![B_2743, E_2742, D_2744, A_2745, B_2741]: (k1_funct_1(k5_relat_1(D_2744, E_2742), A_2745)=k1_funct_1(E_2742, k1_funct_1(D_2744, A_2745)) | k1_xboole_0=B_2741 | ~v1_funct_1(E_2742) | ~v1_relat_1(E_2742) | ~m1_subset_1(D_2744, k1_zfmisc_1(k2_zfmisc_1(B_2743, B_2741))) | ~v1_funct_2(D_2744, B_2743, B_2741) | ~v1_funct_1(D_2744) | v1_xboole_0(B_2743) | ~m1_subset_1(A_2745, B_2743))), inference(resolution, [status(thm)], [c_16, c_19778])).
% 11.41/4.95  tff(c_20768, plain, (![E_2742, A_2745]: (k1_funct_1(k5_relat_1('#skF_5', E_2742), A_2745)=k1_funct_1(E_2742, k1_funct_1('#skF_5', A_2745)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_2742) | ~v1_relat_1(E_2742) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_2745, '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_20754])).
% 11.41/4.95  tff(c_20784, plain, (![E_2742, A_2745]: (k1_funct_1(k5_relat_1('#skF_5', E_2742), A_2745)=k1_funct_1(E_2742, k1_funct_1('#skF_5', A_2745)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_2742) | ~v1_relat_1(E_2742) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_2745, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_20768])).
% 11.41/4.95  tff(c_20793, plain, (![E_2746, A_2747]: (k1_funct_1(k5_relat_1('#skF_5', E_2746), A_2747)=k1_funct_1(E_2746, k1_funct_1('#skF_5', A_2747)) | ~v1_funct_1(E_2746) | ~v1_relat_1(E_2746) | ~m1_subset_1(A_2747, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_309, c_19892, c_20784])).
% 11.41/4.95  tff(c_19891, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_19867])).
% 11.41/4.95  tff(c_36, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.41/4.95  tff(c_19927, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_19891, c_36])).
% 11.41/4.95  tff(c_20803, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20793, c_19927])).
% 11.41/4.95  tff(c_20815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_152, c_46, c_20803])).
% 11.41/4.95  tff(c_20817, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_303])).
% 11.41/4.95  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.41/4.95  tff(c_20824, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_20817, c_6])).
% 11.41/4.95  tff(c_20828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_20824])).
% 11.41/4.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/4.95  
% 11.41/4.95  Inference rules
% 11.41/4.95  ----------------------
% 11.41/4.95  #Ref     : 0
% 11.41/4.95  #Sup     : 4459
% 11.41/4.95  #Fact    : 0
% 11.41/4.95  #Define  : 0
% 11.41/4.95  #Split   : 25
% 11.41/4.95  #Chain   : 0
% 11.41/4.95  #Close   : 0
% 11.41/4.95  
% 11.41/4.95  Ordering : KBO
% 11.41/4.95  
% 11.41/4.95  Simplification rules
% 11.41/4.95  ----------------------
% 11.41/4.95  #Subsume      : 1071
% 11.41/4.95  #Demod        : 1958
% 11.41/4.95  #Tautology    : 835
% 11.41/4.95  #SimpNegUnit  : 39
% 11.41/4.95  #BackRed      : 436
% 11.41/4.95  
% 11.41/4.95  #Partial instantiations: 0
% 11.41/4.95  #Strategies tried      : 1
% 11.41/4.95  
% 11.41/4.95  Timing (in seconds)
% 11.41/4.95  ----------------------
% 11.41/4.95  Preprocessing        : 0.35
% 11.41/4.95  Parsing              : 0.19
% 11.41/4.96  CNF conversion       : 0.03
% 11.41/4.96  Main loop            : 3.83
% 11.41/4.96  Inferencing          : 0.96
% 11.41/4.96  Reduction            : 0.98
% 11.41/4.96  Demodulation         : 0.66
% 11.41/4.96  BG Simplification    : 0.16
% 11.41/4.96  Subsumption          : 1.42
% 11.41/4.96  Abstraction          : 0.23
% 11.41/4.96  MUC search           : 0.00
% 11.41/4.96  Cooper               : 0.00
% 11.41/4.96  Total                : 4.21
% 11.41/4.96  Index Insertion      : 0.00
% 11.41/4.96  Index Deletion       : 0.00
% 11.41/4.96  Index Matching       : 0.00
% 11.41/4.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
