%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:20 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.70s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 452 expanded)
%              Number of leaves         :   41 ( 184 expanded)
%              Depth                    :   12
%              Number of atoms          :  605 (2534 expanded)
%              Number of equality atoms :  107 ( 444 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_tmap_1,type,(
    k1_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_209,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & m1_subset_1(C,k1_zfmisc_1(A)) )
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & m1_subset_1(D,k1_zfmisc_1(A)) )
                   => ( r1_subset_1(C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                             => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),C) = E
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),D) = F ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_167,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(A))
        & ~ v1_xboole_0(D)
        & m1_subset_1(D,k1_zfmisc_1(A))
        & v1_funct_1(E)
        & v1_funct_2(E,C,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,D,B)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
     => ( v1_funct_1(k1_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k1_tmap_1(A,B,C,D,E,F),k4_subset_1(A,C,D),B)
        & m1_subset_1(k1_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_133,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,k4_subset_1(A,C,D),B)
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) )
                               => ( G = k1_tmap_1(A,B,C,D,E,F)
                                <=> ( k2_partfun1(k4_subset_1(A,C,D),B,G,C) = E
                                    & k2_partfun1(k4_subset_1(A,C,D),B,G,D) = F ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_658,plain,(
    ! [C_357,A_358,B_359] :
      ( v1_relat_1(C_357)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(A_358,B_359))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_665,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_658])).

tff(c_81,plain,(
    ! [A_224,B_225] :
      ( r2_hidden('#skF_2'(A_224,B_225),A_224)
      | r1_xboole_0(A_224,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_224,B_225] :
      ( ~ v1_xboole_0(A_224)
      | r1_xboole_0(A_224,B_225) ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_2023,plain,(
    ! [A_629,B_630] :
      ( k7_relat_1(A_629,B_630) = k1_xboole_0
      | ~ r1_xboole_0(B_630,k1_relat_1(A_629))
      | ~ v1_relat_1(A_629) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2039,plain,(
    ! [A_631,A_632] :
      ( k7_relat_1(A_631,A_632) = k1_xboole_0
      | ~ v1_relat_1(A_631)
      | ~ v1_xboole_0(A_632) ) ),
    inference(resolution,[status(thm)],[c_85,c_2023])).

tff(c_2055,plain,(
    ! [A_634] :
      ( k7_relat_1('#skF_8',A_634) = k1_xboole_0
      | ~ v1_xboole_0(A_634) ) ),
    inference(resolution,[status(thm)],[c_665,c_2039])).

tff(c_2059,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2055])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_56,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_2078,plain,(
    ! [A_639,B_640] :
      ( r1_xboole_0(A_639,B_640)
      | ~ r1_subset_1(A_639,B_640)
      | v1_xboole_0(B_640)
      | v1_xboole_0(A_639) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2192,plain,(
    ! [A_657,B_658] :
      ( k3_xboole_0(A_657,B_658) = k1_xboole_0
      | ~ r1_subset_1(A_657,B_658)
      | v1_xboole_0(B_658)
      | v1_xboole_0(A_657) ) ),
    inference(resolution,[status(thm)],[c_2078,c_6])).

tff(c_2195,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2192])).

tff(c_2198,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60,c_2195])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_666,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_658])).

tff(c_2046,plain,(
    ! [A_633] :
      ( k7_relat_1('#skF_7',A_633) = k1_xboole_0
      | ~ v1_xboole_0(A_633) ) ),
    inference(resolution,[status(thm)],[c_666,c_2039])).

tff(c_2050,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2046])).

tff(c_2125,plain,(
    ! [A_647,B_648,C_649] :
      ( k9_subset_1(A_647,B_648,C_649) = k3_xboole_0(B_648,C_649)
      | ~ m1_subset_1(C_649,k1_zfmisc_1(A_647)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2137,plain,(
    ! [B_648] : k9_subset_1('#skF_3',B_648,'#skF_6') = k3_xboole_0(B_648,'#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_2125])).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_52,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_48,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_46,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_2355,plain,(
    ! [F_683,D_684,B_685,E_686,A_688,C_687] :
      ( v1_funct_1(k1_tmap_1(A_688,B_685,C_687,D_684,E_686,F_683))
      | ~ m1_subset_1(F_683,k1_zfmisc_1(k2_zfmisc_1(D_684,B_685)))
      | ~ v1_funct_2(F_683,D_684,B_685)
      | ~ v1_funct_1(F_683)
      | ~ m1_subset_1(E_686,k1_zfmisc_1(k2_zfmisc_1(C_687,B_685)))
      | ~ v1_funct_2(E_686,C_687,B_685)
      | ~ v1_funct_1(E_686)
      | ~ m1_subset_1(D_684,k1_zfmisc_1(A_688))
      | v1_xboole_0(D_684)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(A_688))
      | v1_xboole_0(C_687)
      | v1_xboole_0(B_685)
      | v1_xboole_0(A_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2357,plain,(
    ! [A_688,C_687,E_686] :
      ( v1_funct_1(k1_tmap_1(A_688,'#skF_4',C_687,'#skF_6',E_686,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_686,k1_zfmisc_1(k2_zfmisc_1(C_687,'#skF_4')))
      | ~ v1_funct_2(E_686,C_687,'#skF_4')
      | ~ v1_funct_1(E_686)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_688))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_687,k1_zfmisc_1(A_688))
      | v1_xboole_0(C_687)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_688) ) ),
    inference(resolution,[status(thm)],[c_44,c_2355])).

tff(c_2362,plain,(
    ! [A_688,C_687,E_686] :
      ( v1_funct_1(k1_tmap_1(A_688,'#skF_4',C_687,'#skF_6',E_686,'#skF_8'))
      | ~ m1_subset_1(E_686,k1_zfmisc_1(k2_zfmisc_1(C_687,'#skF_4')))
      | ~ v1_funct_2(E_686,C_687,'#skF_4')
      | ~ v1_funct_1(E_686)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_688))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_687,k1_zfmisc_1(A_688))
      | v1_xboole_0(C_687)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_688) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2357])).

tff(c_2662,plain,(
    ! [A_767,C_768,E_769] :
      ( v1_funct_1(k1_tmap_1(A_767,'#skF_4',C_768,'#skF_6',E_769,'#skF_8'))
      | ~ m1_subset_1(E_769,k1_zfmisc_1(k2_zfmisc_1(C_768,'#skF_4')))
      | ~ v1_funct_2(E_769,C_768,'#skF_4')
      | ~ v1_funct_1(E_769)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_767))
      | ~ m1_subset_1(C_768,k1_zfmisc_1(A_767))
      | v1_xboole_0(C_768)
      | v1_xboole_0(A_767) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_2362])).

tff(c_2669,plain,(
    ! [A_767] :
      ( v1_funct_1(k1_tmap_1(A_767,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_767))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_767))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_767) ) ),
    inference(resolution,[status(thm)],[c_50,c_2662])).

tff(c_2679,plain,(
    ! [A_767] :
      ( v1_funct_1(k1_tmap_1(A_767,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_767))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_767))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_767) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2669])).

tff(c_2688,plain,(
    ! [A_771] :
      ( v1_funct_1(k1_tmap_1(A_771,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_771))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_771))
      | v1_xboole_0(A_771) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2679])).

tff(c_2691,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2688])).

tff(c_2694,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2691])).

tff(c_2695,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2694])).

tff(c_2262,plain,(
    ! [A_669,B_670,C_671,D_672] :
      ( k2_partfun1(A_669,B_670,C_671,D_672) = k7_relat_1(C_671,D_672)
      | ~ m1_subset_1(C_671,k1_zfmisc_1(k2_zfmisc_1(A_669,B_670)))
      | ~ v1_funct_1(C_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2266,plain,(
    ! [D_672] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_672) = k7_relat_1('#skF_7',D_672)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_50,c_2262])).

tff(c_2272,plain,(
    ! [D_672] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_672) = k7_relat_1('#skF_7',D_672) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2266])).

tff(c_2264,plain,(
    ! [D_672] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_672) = k7_relat_1('#skF_8',D_672)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_2262])).

tff(c_2269,plain,(
    ! [D_672] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_672) = k7_relat_1('#skF_8',D_672) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2264])).

tff(c_38,plain,(
    ! [B_155,D_157,A_154,F_159,C_156,E_158] :
      ( v1_funct_2(k1_tmap_1(A_154,B_155,C_156,D_157,E_158,F_159),k4_subset_1(A_154,C_156,D_157),B_155)
      | ~ m1_subset_1(F_159,k1_zfmisc_1(k2_zfmisc_1(D_157,B_155)))
      | ~ v1_funct_2(F_159,D_157,B_155)
      | ~ v1_funct_1(F_159)
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(C_156,B_155)))
      | ~ v1_funct_2(E_158,C_156,B_155)
      | ~ v1_funct_1(E_158)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(A_154))
      | v1_xboole_0(D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(A_154))
      | v1_xboole_0(C_156)
      | v1_xboole_0(B_155)
      | v1_xboole_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_36,plain,(
    ! [B_155,D_157,A_154,F_159,C_156,E_158] :
      ( m1_subset_1(k1_tmap_1(A_154,B_155,C_156,D_157,E_158,F_159),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_154,C_156,D_157),B_155)))
      | ~ m1_subset_1(F_159,k1_zfmisc_1(k2_zfmisc_1(D_157,B_155)))
      | ~ v1_funct_2(F_159,D_157,B_155)
      | ~ v1_funct_1(F_159)
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(C_156,B_155)))
      | ~ v1_funct_2(E_158,C_156,B_155)
      | ~ v1_funct_1(E_158)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(A_154))
      | v1_xboole_0(D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(A_154))
      | v1_xboole_0(C_156)
      | v1_xboole_0(B_155)
      | v1_xboole_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2632,plain,(
    ! [B_754,C_757,D_756,E_759,A_758,F_755] :
      ( k2_partfun1(k4_subset_1(A_758,C_757,D_756),B_754,k1_tmap_1(A_758,B_754,C_757,D_756,E_759,F_755),C_757) = E_759
      | ~ m1_subset_1(k1_tmap_1(A_758,B_754,C_757,D_756,E_759,F_755),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_758,C_757,D_756),B_754)))
      | ~ v1_funct_2(k1_tmap_1(A_758,B_754,C_757,D_756,E_759,F_755),k4_subset_1(A_758,C_757,D_756),B_754)
      | ~ v1_funct_1(k1_tmap_1(A_758,B_754,C_757,D_756,E_759,F_755))
      | k2_partfun1(D_756,B_754,F_755,k9_subset_1(A_758,C_757,D_756)) != k2_partfun1(C_757,B_754,E_759,k9_subset_1(A_758,C_757,D_756))
      | ~ m1_subset_1(F_755,k1_zfmisc_1(k2_zfmisc_1(D_756,B_754)))
      | ~ v1_funct_2(F_755,D_756,B_754)
      | ~ v1_funct_1(F_755)
      | ~ m1_subset_1(E_759,k1_zfmisc_1(k2_zfmisc_1(C_757,B_754)))
      | ~ v1_funct_2(E_759,C_757,B_754)
      | ~ v1_funct_1(E_759)
      | ~ m1_subset_1(D_756,k1_zfmisc_1(A_758))
      | v1_xboole_0(D_756)
      | ~ m1_subset_1(C_757,k1_zfmisc_1(A_758))
      | v1_xboole_0(C_757)
      | v1_xboole_0(B_754)
      | v1_xboole_0(A_758) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3182,plain,(
    ! [C_855,A_856,F_851,E_854,D_852,B_853] :
      ( k2_partfun1(k4_subset_1(A_856,C_855,D_852),B_853,k1_tmap_1(A_856,B_853,C_855,D_852,E_854,F_851),C_855) = E_854
      | ~ v1_funct_2(k1_tmap_1(A_856,B_853,C_855,D_852,E_854,F_851),k4_subset_1(A_856,C_855,D_852),B_853)
      | ~ v1_funct_1(k1_tmap_1(A_856,B_853,C_855,D_852,E_854,F_851))
      | k2_partfun1(D_852,B_853,F_851,k9_subset_1(A_856,C_855,D_852)) != k2_partfun1(C_855,B_853,E_854,k9_subset_1(A_856,C_855,D_852))
      | ~ m1_subset_1(F_851,k1_zfmisc_1(k2_zfmisc_1(D_852,B_853)))
      | ~ v1_funct_2(F_851,D_852,B_853)
      | ~ v1_funct_1(F_851)
      | ~ m1_subset_1(E_854,k1_zfmisc_1(k2_zfmisc_1(C_855,B_853)))
      | ~ v1_funct_2(E_854,C_855,B_853)
      | ~ v1_funct_1(E_854)
      | ~ m1_subset_1(D_852,k1_zfmisc_1(A_856))
      | v1_xboole_0(D_852)
      | ~ m1_subset_1(C_855,k1_zfmisc_1(A_856))
      | v1_xboole_0(C_855)
      | v1_xboole_0(B_853)
      | v1_xboole_0(A_856) ) ),
    inference(resolution,[status(thm)],[c_36,c_2632])).

tff(c_3290,plain,(
    ! [C_878,F_874,A_879,E_877,D_875,B_876] :
      ( k2_partfun1(k4_subset_1(A_879,C_878,D_875),B_876,k1_tmap_1(A_879,B_876,C_878,D_875,E_877,F_874),C_878) = E_877
      | ~ v1_funct_1(k1_tmap_1(A_879,B_876,C_878,D_875,E_877,F_874))
      | k2_partfun1(D_875,B_876,F_874,k9_subset_1(A_879,C_878,D_875)) != k2_partfun1(C_878,B_876,E_877,k9_subset_1(A_879,C_878,D_875))
      | ~ m1_subset_1(F_874,k1_zfmisc_1(k2_zfmisc_1(D_875,B_876)))
      | ~ v1_funct_2(F_874,D_875,B_876)
      | ~ v1_funct_1(F_874)
      | ~ m1_subset_1(E_877,k1_zfmisc_1(k2_zfmisc_1(C_878,B_876)))
      | ~ v1_funct_2(E_877,C_878,B_876)
      | ~ v1_funct_1(E_877)
      | ~ m1_subset_1(D_875,k1_zfmisc_1(A_879))
      | v1_xboole_0(D_875)
      | ~ m1_subset_1(C_878,k1_zfmisc_1(A_879))
      | v1_xboole_0(C_878)
      | v1_xboole_0(B_876)
      | v1_xboole_0(A_879) ) ),
    inference(resolution,[status(thm)],[c_38,c_3182])).

tff(c_3294,plain,(
    ! [A_879,C_878,E_877] :
      ( k2_partfun1(k4_subset_1(A_879,C_878,'#skF_6'),'#skF_4',k1_tmap_1(A_879,'#skF_4',C_878,'#skF_6',E_877,'#skF_8'),C_878) = E_877
      | ~ v1_funct_1(k1_tmap_1(A_879,'#skF_4',C_878,'#skF_6',E_877,'#skF_8'))
      | k2_partfun1(C_878,'#skF_4',E_877,k9_subset_1(A_879,C_878,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_879,C_878,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_877,k1_zfmisc_1(k2_zfmisc_1(C_878,'#skF_4')))
      | ~ v1_funct_2(E_877,C_878,'#skF_4')
      | ~ v1_funct_1(E_877)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_879))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_878,k1_zfmisc_1(A_879))
      | v1_xboole_0(C_878)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_879) ) ),
    inference(resolution,[status(thm)],[c_44,c_3290])).

tff(c_3300,plain,(
    ! [A_879,C_878,E_877] :
      ( k2_partfun1(k4_subset_1(A_879,C_878,'#skF_6'),'#skF_4',k1_tmap_1(A_879,'#skF_4',C_878,'#skF_6',E_877,'#skF_8'),C_878) = E_877
      | ~ v1_funct_1(k1_tmap_1(A_879,'#skF_4',C_878,'#skF_6',E_877,'#skF_8'))
      | k2_partfun1(C_878,'#skF_4',E_877,k9_subset_1(A_879,C_878,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_879,C_878,'#skF_6'))
      | ~ m1_subset_1(E_877,k1_zfmisc_1(k2_zfmisc_1(C_878,'#skF_4')))
      | ~ v1_funct_2(E_877,C_878,'#skF_4')
      | ~ v1_funct_1(E_877)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_879))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_878,k1_zfmisc_1(A_879))
      | v1_xboole_0(C_878)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_879) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2269,c_3294])).

tff(c_3306,plain,(
    ! [A_880,C_881,E_882] :
      ( k2_partfun1(k4_subset_1(A_880,C_881,'#skF_6'),'#skF_4',k1_tmap_1(A_880,'#skF_4',C_881,'#skF_6',E_882,'#skF_8'),C_881) = E_882
      | ~ v1_funct_1(k1_tmap_1(A_880,'#skF_4',C_881,'#skF_6',E_882,'#skF_8'))
      | k2_partfun1(C_881,'#skF_4',E_882,k9_subset_1(A_880,C_881,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_880,C_881,'#skF_6'))
      | ~ m1_subset_1(E_882,k1_zfmisc_1(k2_zfmisc_1(C_881,'#skF_4')))
      | ~ v1_funct_2(E_882,C_881,'#skF_4')
      | ~ v1_funct_1(E_882)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_880))
      | ~ m1_subset_1(C_881,k1_zfmisc_1(A_880))
      | v1_xboole_0(C_881)
      | v1_xboole_0(A_880) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_3300])).

tff(c_3313,plain,(
    ! [A_880] :
      ( k2_partfun1(k4_subset_1(A_880,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_880,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_880,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_880,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_880,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_880))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_880))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_880) ) ),
    inference(resolution,[status(thm)],[c_50,c_3306])).

tff(c_3323,plain,(
    ! [A_880] :
      ( k2_partfun1(k4_subset_1(A_880,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_880,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_880,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_880,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_880,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_880))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_880))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_880) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2272,c_3313])).

tff(c_3325,plain,(
    ! [A_883] :
      ( k2_partfun1(k4_subset_1(A_883,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_883,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_883,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_883,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_883,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_883))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_883))
      | v1_xboole_0(A_883) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3323])).

tff(c_732,plain,(
    ! [A_374,B_375] :
      ( k7_relat_1(A_374,B_375) = k1_xboole_0
      | ~ r1_xboole_0(B_375,k1_relat_1(A_374))
      | ~ v1_relat_1(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_785,plain,(
    ! [A_381,A_382] :
      ( k7_relat_1(A_381,A_382) = k1_xboole_0
      | ~ v1_relat_1(A_381)
      | ~ v1_xboole_0(A_382) ) ),
    inference(resolution,[status(thm)],[c_85,c_732])).

tff(c_810,plain,(
    ! [A_385] :
      ( k7_relat_1('#skF_8',A_385) = k1_xboole_0
      | ~ v1_xboole_0(A_385) ) ),
    inference(resolution,[status(thm)],[c_665,c_785])).

tff(c_814,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_810])).

tff(c_707,plain,(
    ! [A_370,B_371] :
      ( r1_xboole_0(A_370,B_371)
      | ~ r1_subset_1(A_370,B_371)
      | v1_xboole_0(B_371)
      | v1_xboole_0(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_877,plain,(
    ! [A_400,B_401] :
      ( k3_xboole_0(A_400,B_401) = k1_xboole_0
      | ~ r1_subset_1(A_400,B_401)
      | v1_xboole_0(B_401)
      | v1_xboole_0(A_400) ) ),
    inference(resolution,[status(thm)],[c_707,c_6])).

tff(c_883,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_877])).

tff(c_887,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60,c_883])).

tff(c_801,plain,(
    ! [A_384] :
      ( k7_relat_1('#skF_7',A_384) = k1_xboole_0
      | ~ v1_xboole_0(A_384) ) ),
    inference(resolution,[status(thm)],[c_666,c_785])).

tff(c_805,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_801])).

tff(c_753,plain,(
    ! [A_376,B_377,C_378] :
      ( k9_subset_1(A_376,B_377,C_378) = k3_xboole_0(B_377,C_378)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(A_376)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_765,plain,(
    ! [B_377] : k9_subset_1('#skF_3',B_377,'#skF_6') = k3_xboole_0(B_377,'#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_753])).

tff(c_978,plain,(
    ! [F_416,C_420,B_418,A_421,E_419,D_417] :
      ( v1_funct_1(k1_tmap_1(A_421,B_418,C_420,D_417,E_419,F_416))
      | ~ m1_subset_1(F_416,k1_zfmisc_1(k2_zfmisc_1(D_417,B_418)))
      | ~ v1_funct_2(F_416,D_417,B_418)
      | ~ v1_funct_1(F_416)
      | ~ m1_subset_1(E_419,k1_zfmisc_1(k2_zfmisc_1(C_420,B_418)))
      | ~ v1_funct_2(E_419,C_420,B_418)
      | ~ v1_funct_1(E_419)
      | ~ m1_subset_1(D_417,k1_zfmisc_1(A_421))
      | v1_xboole_0(D_417)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(A_421))
      | v1_xboole_0(C_420)
      | v1_xboole_0(B_418)
      | v1_xboole_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_980,plain,(
    ! [A_421,C_420,E_419] :
      ( v1_funct_1(k1_tmap_1(A_421,'#skF_4',C_420,'#skF_6',E_419,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_419,k1_zfmisc_1(k2_zfmisc_1(C_420,'#skF_4')))
      | ~ v1_funct_2(E_419,C_420,'#skF_4')
      | ~ v1_funct_1(E_419)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_421))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_420,k1_zfmisc_1(A_421))
      | v1_xboole_0(C_420)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_421) ) ),
    inference(resolution,[status(thm)],[c_44,c_978])).

tff(c_985,plain,(
    ! [A_421,C_420,E_419] :
      ( v1_funct_1(k1_tmap_1(A_421,'#skF_4',C_420,'#skF_6',E_419,'#skF_8'))
      | ~ m1_subset_1(E_419,k1_zfmisc_1(k2_zfmisc_1(C_420,'#skF_4')))
      | ~ v1_funct_2(E_419,C_420,'#skF_4')
      | ~ v1_funct_1(E_419)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_421))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_420,k1_zfmisc_1(A_421))
      | v1_xboole_0(C_420)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_980])).

tff(c_1294,plain,(
    ! [A_492,C_493,E_494] :
      ( v1_funct_1(k1_tmap_1(A_492,'#skF_4',C_493,'#skF_6',E_494,'#skF_8'))
      | ~ m1_subset_1(E_494,k1_zfmisc_1(k2_zfmisc_1(C_493,'#skF_4')))
      | ~ v1_funct_2(E_494,C_493,'#skF_4')
      | ~ v1_funct_1(E_494)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_492))
      | ~ m1_subset_1(C_493,k1_zfmisc_1(A_492))
      | v1_xboole_0(C_493)
      | v1_xboole_0(A_492) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_985])).

tff(c_1301,plain,(
    ! [A_492] :
      ( v1_funct_1(k1_tmap_1(A_492,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_492))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_492))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_492) ) ),
    inference(resolution,[status(thm)],[c_50,c_1294])).

tff(c_1311,plain,(
    ! [A_492] :
      ( v1_funct_1(k1_tmap_1(A_492,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_492))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_492))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_492) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1301])).

tff(c_1377,plain,(
    ! [A_518] :
      ( v1_funct_1(k1_tmap_1(A_518,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_518))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_518))
      | v1_xboole_0(A_518) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1311])).

tff(c_1380,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1377])).

tff(c_1383,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1380])).

tff(c_1384,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1383])).

tff(c_888,plain,(
    ! [A_402,B_403,C_404,D_405] :
      ( k2_partfun1(A_402,B_403,C_404,D_405) = k7_relat_1(C_404,D_405)
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(C_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_892,plain,(
    ! [D_405] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_405) = k7_relat_1('#skF_7',D_405)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_50,c_888])).

tff(c_898,plain,(
    ! [D_405] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_405) = k7_relat_1('#skF_7',D_405) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_892])).

tff(c_890,plain,(
    ! [D_405] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_405) = k7_relat_1('#skF_8',D_405)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_888])).

tff(c_895,plain,(
    ! [D_405] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_405) = k7_relat_1('#skF_8',D_405) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_890])).

tff(c_1246,plain,(
    ! [E_487,B_482,A_486,D_484,F_483,C_485] :
      ( k2_partfun1(k4_subset_1(A_486,C_485,D_484),B_482,k1_tmap_1(A_486,B_482,C_485,D_484,E_487,F_483),D_484) = F_483
      | ~ m1_subset_1(k1_tmap_1(A_486,B_482,C_485,D_484,E_487,F_483),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_486,C_485,D_484),B_482)))
      | ~ v1_funct_2(k1_tmap_1(A_486,B_482,C_485,D_484,E_487,F_483),k4_subset_1(A_486,C_485,D_484),B_482)
      | ~ v1_funct_1(k1_tmap_1(A_486,B_482,C_485,D_484,E_487,F_483))
      | k2_partfun1(D_484,B_482,F_483,k9_subset_1(A_486,C_485,D_484)) != k2_partfun1(C_485,B_482,E_487,k9_subset_1(A_486,C_485,D_484))
      | ~ m1_subset_1(F_483,k1_zfmisc_1(k2_zfmisc_1(D_484,B_482)))
      | ~ v1_funct_2(F_483,D_484,B_482)
      | ~ v1_funct_1(F_483)
      | ~ m1_subset_1(E_487,k1_zfmisc_1(k2_zfmisc_1(C_485,B_482)))
      | ~ v1_funct_2(E_487,C_485,B_482)
      | ~ v1_funct_1(E_487)
      | ~ m1_subset_1(D_484,k1_zfmisc_1(A_486))
      | v1_xboole_0(D_484)
      | ~ m1_subset_1(C_485,k1_zfmisc_1(A_486))
      | v1_xboole_0(C_485)
      | v1_xboole_0(B_482)
      | v1_xboole_0(A_486) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1794,plain,(
    ! [E_594,C_595,B_593,D_592,F_591,A_596] :
      ( k2_partfun1(k4_subset_1(A_596,C_595,D_592),B_593,k1_tmap_1(A_596,B_593,C_595,D_592,E_594,F_591),D_592) = F_591
      | ~ v1_funct_2(k1_tmap_1(A_596,B_593,C_595,D_592,E_594,F_591),k4_subset_1(A_596,C_595,D_592),B_593)
      | ~ v1_funct_1(k1_tmap_1(A_596,B_593,C_595,D_592,E_594,F_591))
      | k2_partfun1(D_592,B_593,F_591,k9_subset_1(A_596,C_595,D_592)) != k2_partfun1(C_595,B_593,E_594,k9_subset_1(A_596,C_595,D_592))
      | ~ m1_subset_1(F_591,k1_zfmisc_1(k2_zfmisc_1(D_592,B_593)))
      | ~ v1_funct_2(F_591,D_592,B_593)
      | ~ v1_funct_1(F_591)
      | ~ m1_subset_1(E_594,k1_zfmisc_1(k2_zfmisc_1(C_595,B_593)))
      | ~ v1_funct_2(E_594,C_595,B_593)
      | ~ v1_funct_1(E_594)
      | ~ m1_subset_1(D_592,k1_zfmisc_1(A_596))
      | v1_xboole_0(D_592)
      | ~ m1_subset_1(C_595,k1_zfmisc_1(A_596))
      | v1_xboole_0(C_595)
      | v1_xboole_0(B_593)
      | v1_xboole_0(A_596) ) ),
    inference(resolution,[status(thm)],[c_36,c_1246])).

tff(c_1933,plain,(
    ! [B_617,D_616,E_618,A_620,F_615,C_619] :
      ( k2_partfun1(k4_subset_1(A_620,C_619,D_616),B_617,k1_tmap_1(A_620,B_617,C_619,D_616,E_618,F_615),D_616) = F_615
      | ~ v1_funct_1(k1_tmap_1(A_620,B_617,C_619,D_616,E_618,F_615))
      | k2_partfun1(D_616,B_617,F_615,k9_subset_1(A_620,C_619,D_616)) != k2_partfun1(C_619,B_617,E_618,k9_subset_1(A_620,C_619,D_616))
      | ~ m1_subset_1(F_615,k1_zfmisc_1(k2_zfmisc_1(D_616,B_617)))
      | ~ v1_funct_2(F_615,D_616,B_617)
      | ~ v1_funct_1(F_615)
      | ~ m1_subset_1(E_618,k1_zfmisc_1(k2_zfmisc_1(C_619,B_617)))
      | ~ v1_funct_2(E_618,C_619,B_617)
      | ~ v1_funct_1(E_618)
      | ~ m1_subset_1(D_616,k1_zfmisc_1(A_620))
      | v1_xboole_0(D_616)
      | ~ m1_subset_1(C_619,k1_zfmisc_1(A_620))
      | v1_xboole_0(C_619)
      | v1_xboole_0(B_617)
      | v1_xboole_0(A_620) ) ),
    inference(resolution,[status(thm)],[c_38,c_1794])).

tff(c_1937,plain,(
    ! [A_620,C_619,E_618] :
      ( k2_partfun1(k4_subset_1(A_620,C_619,'#skF_6'),'#skF_4',k1_tmap_1(A_620,'#skF_4',C_619,'#skF_6',E_618,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_620,'#skF_4',C_619,'#skF_6',E_618,'#skF_8'))
      | k2_partfun1(C_619,'#skF_4',E_618,k9_subset_1(A_620,C_619,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_620,C_619,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_618,k1_zfmisc_1(k2_zfmisc_1(C_619,'#skF_4')))
      | ~ v1_funct_2(E_618,C_619,'#skF_4')
      | ~ v1_funct_1(E_618)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_620))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_619,k1_zfmisc_1(A_620))
      | v1_xboole_0(C_619)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_620) ) ),
    inference(resolution,[status(thm)],[c_44,c_1933])).

tff(c_1943,plain,(
    ! [A_620,C_619,E_618] :
      ( k2_partfun1(k4_subset_1(A_620,C_619,'#skF_6'),'#skF_4',k1_tmap_1(A_620,'#skF_4',C_619,'#skF_6',E_618,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_620,'#skF_4',C_619,'#skF_6',E_618,'#skF_8'))
      | k2_partfun1(C_619,'#skF_4',E_618,k9_subset_1(A_620,C_619,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_620,C_619,'#skF_6'))
      | ~ m1_subset_1(E_618,k1_zfmisc_1(k2_zfmisc_1(C_619,'#skF_4')))
      | ~ v1_funct_2(E_618,C_619,'#skF_4')
      | ~ v1_funct_1(E_618)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_620))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_619,k1_zfmisc_1(A_620))
      | v1_xboole_0(C_619)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_620) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_895,c_1937])).

tff(c_1949,plain,(
    ! [A_621,C_622,E_623] :
      ( k2_partfun1(k4_subset_1(A_621,C_622,'#skF_6'),'#skF_4',k1_tmap_1(A_621,'#skF_4',C_622,'#skF_6',E_623,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_621,'#skF_4',C_622,'#skF_6',E_623,'#skF_8'))
      | k2_partfun1(C_622,'#skF_4',E_623,k9_subset_1(A_621,C_622,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_621,C_622,'#skF_6'))
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(C_622,'#skF_4')))
      | ~ v1_funct_2(E_623,C_622,'#skF_4')
      | ~ v1_funct_1(E_623)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_621))
      | ~ m1_subset_1(C_622,k1_zfmisc_1(A_621))
      | v1_xboole_0(C_622)
      | v1_xboole_0(A_621) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1943])).

tff(c_1956,plain,(
    ! [A_621] :
      ( k2_partfun1(k4_subset_1(A_621,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_621,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_621,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_621,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_621,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_621))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_621))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_621) ) ),
    inference(resolution,[status(thm)],[c_50,c_1949])).

tff(c_1966,plain,(
    ! [A_621] :
      ( k2_partfun1(k4_subset_1(A_621,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_621,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_621,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_621,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_621,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_621))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_621))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_898,c_1956])).

tff(c_1968,plain,(
    ! [A_624] :
      ( k2_partfun1(k4_subset_1(A_624,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_624,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_624,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_624,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_624,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_624))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_624))
      | v1_xboole_0(A_624) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1966])).

tff(c_103,plain,(
    ! [C_231,A_232,B_233] :
      ( v1_relat_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_110,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_164,plain,(
    ! [A_246,B_247] :
      ( k7_relat_1(A_246,B_247) = k1_xboole_0
      | ~ r1_xboole_0(B_247,k1_relat_1(A_246))
      | ~ v1_relat_1(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_180,plain,(
    ! [A_248,A_249] :
      ( k7_relat_1(A_248,A_249) = k1_xboole_0
      | ~ v1_relat_1(A_248)
      | ~ v1_xboole_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_85,c_164])).

tff(c_213,plain,(
    ! [A_253] :
      ( k7_relat_1('#skF_8',A_253) = k1_xboole_0
      | ~ v1_xboole_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_110,c_180])).

tff(c_217,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_213])).

tff(c_187,plain,(
    ! [A_250,B_251] :
      ( r1_xboole_0(A_250,B_251)
      | ~ r1_subset_1(A_250,B_251)
      | v1_xboole_0(B_251)
      | v1_xboole_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_329,plain,(
    ! [A_277,B_278] :
      ( k3_xboole_0(A_277,B_278) = k1_xboole_0
      | ~ r1_subset_1(A_277,B_278)
      | v1_xboole_0(B_278)
      | v1_xboole_0(A_277) ) ),
    inference(resolution,[status(thm)],[c_187,c_6])).

tff(c_335,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_329])).

tff(c_339,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60,c_335])).

tff(c_111,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_103])).

tff(c_204,plain,(
    ! [A_252] :
      ( k7_relat_1('#skF_7',A_252) = k1_xboole_0
      | ~ v1_xboole_0(A_252) ) ),
    inference(resolution,[status(thm)],[c_111,c_180])).

tff(c_208,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_204])).

tff(c_262,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( k2_partfun1(A_265,B_266,C_267,D_268) = k7_relat_1(C_267,D_268)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_1(C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_266,plain,(
    ! [D_268] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_268) = k7_relat_1('#skF_7',D_268)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_50,c_262])).

tff(c_272,plain,(
    ! [D_268] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_268) = k7_relat_1('#skF_7',D_268) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_266])).

tff(c_264,plain,(
    ! [D_268] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_268) = k7_relat_1('#skF_8',D_268)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_262])).

tff(c_269,plain,(
    ! [D_268] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_268) = k7_relat_1('#skF_8',D_268) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_264])).

tff(c_249,plain,(
    ! [A_262,B_263,C_264] :
      ( k9_subset_1(A_262,B_263,C_264) = k3_xboole_0(B_263,C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(A_262)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_261,plain,(
    ! [B_263] : k9_subset_1('#skF_3',B_263,'#skF_6') = k3_xboole_0(B_263,'#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_249])).

tff(c_42,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_86,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_282,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_261,c_86])).

tff(c_635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_339,c_208,c_339,c_272,c_269,c_282])).

tff(c_636,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_681,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_636])).

tff(c_1979,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1968,c_681])).

tff(c_1993,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_814,c_887,c_805,c_887,c_765,c_765,c_1384,c_1979])).

tff(c_1995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1993])).

tff(c_1996,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_636])).

tff(c_3334,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3325,c_1996])).

tff(c_3345,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_2059,c_2198,c_2050,c_2198,c_2137,c_2137,c_2695,c_3334])).

tff(c_3347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.43/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.31  
% 6.70/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.31  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 6.70/2.31  
% 6.70/2.31  %Foreground sorts:
% 6.70/2.31  
% 6.70/2.31  
% 6.70/2.31  %Background operators:
% 6.70/2.31  
% 6.70/2.31  
% 6.70/2.31  %Foreground operators:
% 6.70/2.31  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 6.70/2.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.70/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.70/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.70/2.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.70/2.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.70/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.70/2.31  tff('#skF_7', type, '#skF_7': $i).
% 6.70/2.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.70/2.31  tff('#skF_5', type, '#skF_5': $i).
% 6.70/2.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.70/2.31  tff('#skF_6', type, '#skF_6': $i).
% 6.70/2.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.70/2.31  tff('#skF_3', type, '#skF_3': $i).
% 6.70/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.70/2.31  tff('#skF_8', type, '#skF_8': $i).
% 6.70/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.70/2.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.70/2.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.70/2.31  tff('#skF_4', type, '#skF_4': $i).
% 6.70/2.31  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.70/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.70/2.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.70/2.31  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.70/2.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.70/2.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.70/2.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.70/2.31  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.70/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.70/2.31  
% 6.70/2.34  tff(f_209, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 6.70/2.34  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.70/2.34  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.70/2.34  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.70/2.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.70/2.34  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 6.70/2.34  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 6.70/2.34  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.70/2.34  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.70/2.34  tff(f_167, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 6.70/2.34  tff(f_85, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.70/2.34  tff(f_133, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 6.70/2.34  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.70/2.34  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_658, plain, (![C_357, A_358, B_359]: (v1_relat_1(C_357) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(A_358, B_359))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.70/2.34  tff(c_665, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_658])).
% 6.70/2.34  tff(c_81, plain, (![A_224, B_225]: (r2_hidden('#skF_2'(A_224, B_225), A_224) | r1_xboole_0(A_224, B_225))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.70/2.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.70/2.34  tff(c_85, plain, (![A_224, B_225]: (~v1_xboole_0(A_224) | r1_xboole_0(A_224, B_225))), inference(resolution, [status(thm)], [c_81, c_2])).
% 6.70/2.34  tff(c_2023, plain, (![A_629, B_630]: (k7_relat_1(A_629, B_630)=k1_xboole_0 | ~r1_xboole_0(B_630, k1_relat_1(A_629)) | ~v1_relat_1(A_629))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.70/2.34  tff(c_2039, plain, (![A_631, A_632]: (k7_relat_1(A_631, A_632)=k1_xboole_0 | ~v1_relat_1(A_631) | ~v1_xboole_0(A_632))), inference(resolution, [status(thm)], [c_85, c_2023])).
% 6.70/2.34  tff(c_2055, plain, (![A_634]: (k7_relat_1('#skF_8', A_634)=k1_xboole_0 | ~v1_xboole_0(A_634))), inference(resolution, [status(thm)], [c_665, c_2039])).
% 6.70/2.34  tff(c_2059, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_2055])).
% 6.70/2.34  tff(c_64, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_60, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_56, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_2078, plain, (![A_639, B_640]: (r1_xboole_0(A_639, B_640) | ~r1_subset_1(A_639, B_640) | v1_xboole_0(B_640) | v1_xboole_0(A_639))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.70/2.34  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.70/2.34  tff(c_2192, plain, (![A_657, B_658]: (k3_xboole_0(A_657, B_658)=k1_xboole_0 | ~r1_subset_1(A_657, B_658) | v1_xboole_0(B_658) | v1_xboole_0(A_657))), inference(resolution, [status(thm)], [c_2078, c_6])).
% 6.70/2.34  tff(c_2195, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2192])).
% 6.70/2.34  tff(c_2198, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_60, c_2195])).
% 6.70/2.34  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_666, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_658])).
% 6.70/2.34  tff(c_2046, plain, (![A_633]: (k7_relat_1('#skF_7', A_633)=k1_xboole_0 | ~v1_xboole_0(A_633))), inference(resolution, [status(thm)], [c_666, c_2039])).
% 6.70/2.34  tff(c_2050, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_2046])).
% 6.70/2.34  tff(c_2125, plain, (![A_647, B_648, C_649]: (k9_subset_1(A_647, B_648, C_649)=k3_xboole_0(B_648, C_649) | ~m1_subset_1(C_649, k1_zfmisc_1(A_647)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.70/2.34  tff(c_2137, plain, (![B_648]: (k9_subset_1('#skF_3', B_648, '#skF_6')=k3_xboole_0(B_648, '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_2125])).
% 6.70/2.34  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_52, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_48, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_46, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_2355, plain, (![F_683, D_684, B_685, E_686, A_688, C_687]: (v1_funct_1(k1_tmap_1(A_688, B_685, C_687, D_684, E_686, F_683)) | ~m1_subset_1(F_683, k1_zfmisc_1(k2_zfmisc_1(D_684, B_685))) | ~v1_funct_2(F_683, D_684, B_685) | ~v1_funct_1(F_683) | ~m1_subset_1(E_686, k1_zfmisc_1(k2_zfmisc_1(C_687, B_685))) | ~v1_funct_2(E_686, C_687, B_685) | ~v1_funct_1(E_686) | ~m1_subset_1(D_684, k1_zfmisc_1(A_688)) | v1_xboole_0(D_684) | ~m1_subset_1(C_687, k1_zfmisc_1(A_688)) | v1_xboole_0(C_687) | v1_xboole_0(B_685) | v1_xboole_0(A_688))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.70/2.34  tff(c_2357, plain, (![A_688, C_687, E_686]: (v1_funct_1(k1_tmap_1(A_688, '#skF_4', C_687, '#skF_6', E_686, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_686, k1_zfmisc_1(k2_zfmisc_1(C_687, '#skF_4'))) | ~v1_funct_2(E_686, C_687, '#skF_4') | ~v1_funct_1(E_686) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_688)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_687, k1_zfmisc_1(A_688)) | v1_xboole_0(C_687) | v1_xboole_0('#skF_4') | v1_xboole_0(A_688))), inference(resolution, [status(thm)], [c_44, c_2355])).
% 6.70/2.34  tff(c_2362, plain, (![A_688, C_687, E_686]: (v1_funct_1(k1_tmap_1(A_688, '#skF_4', C_687, '#skF_6', E_686, '#skF_8')) | ~m1_subset_1(E_686, k1_zfmisc_1(k2_zfmisc_1(C_687, '#skF_4'))) | ~v1_funct_2(E_686, C_687, '#skF_4') | ~v1_funct_1(E_686) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_688)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_687, k1_zfmisc_1(A_688)) | v1_xboole_0(C_687) | v1_xboole_0('#skF_4') | v1_xboole_0(A_688))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2357])).
% 6.70/2.34  tff(c_2662, plain, (![A_767, C_768, E_769]: (v1_funct_1(k1_tmap_1(A_767, '#skF_4', C_768, '#skF_6', E_769, '#skF_8')) | ~m1_subset_1(E_769, k1_zfmisc_1(k2_zfmisc_1(C_768, '#skF_4'))) | ~v1_funct_2(E_769, C_768, '#skF_4') | ~v1_funct_1(E_769) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_767)) | ~m1_subset_1(C_768, k1_zfmisc_1(A_767)) | v1_xboole_0(C_768) | v1_xboole_0(A_767))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_2362])).
% 6.70/2.34  tff(c_2669, plain, (![A_767]: (v1_funct_1(k1_tmap_1(A_767, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_767)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_767)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_767))), inference(resolution, [status(thm)], [c_50, c_2662])).
% 6.70/2.34  tff(c_2679, plain, (![A_767]: (v1_funct_1(k1_tmap_1(A_767, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_767)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_767)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_767))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2669])).
% 6.70/2.34  tff(c_2688, plain, (![A_771]: (v1_funct_1(k1_tmap_1(A_771, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_771)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_771)) | v1_xboole_0(A_771))), inference(negUnitSimplification, [status(thm)], [c_64, c_2679])).
% 6.70/2.34  tff(c_2691, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2688])).
% 6.70/2.34  tff(c_2694, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2691])).
% 6.70/2.34  tff(c_2695, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_68, c_2694])).
% 6.70/2.34  tff(c_2262, plain, (![A_669, B_670, C_671, D_672]: (k2_partfun1(A_669, B_670, C_671, D_672)=k7_relat_1(C_671, D_672) | ~m1_subset_1(C_671, k1_zfmisc_1(k2_zfmisc_1(A_669, B_670))) | ~v1_funct_1(C_671))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.70/2.34  tff(c_2266, plain, (![D_672]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_672)=k7_relat_1('#skF_7', D_672) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_50, c_2262])).
% 6.70/2.34  tff(c_2272, plain, (![D_672]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_672)=k7_relat_1('#skF_7', D_672))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2266])).
% 6.70/2.34  tff(c_2264, plain, (![D_672]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_672)=k7_relat_1('#skF_8', D_672) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_44, c_2262])).
% 6.70/2.34  tff(c_2269, plain, (![D_672]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_672)=k7_relat_1('#skF_8', D_672))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2264])).
% 6.70/2.34  tff(c_38, plain, (![B_155, D_157, A_154, F_159, C_156, E_158]: (v1_funct_2(k1_tmap_1(A_154, B_155, C_156, D_157, E_158, F_159), k4_subset_1(A_154, C_156, D_157), B_155) | ~m1_subset_1(F_159, k1_zfmisc_1(k2_zfmisc_1(D_157, B_155))) | ~v1_funct_2(F_159, D_157, B_155) | ~v1_funct_1(F_159) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(C_156, B_155))) | ~v1_funct_2(E_158, C_156, B_155) | ~v1_funct_1(E_158) | ~m1_subset_1(D_157, k1_zfmisc_1(A_154)) | v1_xboole_0(D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(A_154)) | v1_xboole_0(C_156) | v1_xboole_0(B_155) | v1_xboole_0(A_154))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.70/2.34  tff(c_36, plain, (![B_155, D_157, A_154, F_159, C_156, E_158]: (m1_subset_1(k1_tmap_1(A_154, B_155, C_156, D_157, E_158, F_159), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_154, C_156, D_157), B_155))) | ~m1_subset_1(F_159, k1_zfmisc_1(k2_zfmisc_1(D_157, B_155))) | ~v1_funct_2(F_159, D_157, B_155) | ~v1_funct_1(F_159) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(C_156, B_155))) | ~v1_funct_2(E_158, C_156, B_155) | ~v1_funct_1(E_158) | ~m1_subset_1(D_157, k1_zfmisc_1(A_154)) | v1_xboole_0(D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(A_154)) | v1_xboole_0(C_156) | v1_xboole_0(B_155) | v1_xboole_0(A_154))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.70/2.34  tff(c_2632, plain, (![B_754, C_757, D_756, E_759, A_758, F_755]: (k2_partfun1(k4_subset_1(A_758, C_757, D_756), B_754, k1_tmap_1(A_758, B_754, C_757, D_756, E_759, F_755), C_757)=E_759 | ~m1_subset_1(k1_tmap_1(A_758, B_754, C_757, D_756, E_759, F_755), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_758, C_757, D_756), B_754))) | ~v1_funct_2(k1_tmap_1(A_758, B_754, C_757, D_756, E_759, F_755), k4_subset_1(A_758, C_757, D_756), B_754) | ~v1_funct_1(k1_tmap_1(A_758, B_754, C_757, D_756, E_759, F_755)) | k2_partfun1(D_756, B_754, F_755, k9_subset_1(A_758, C_757, D_756))!=k2_partfun1(C_757, B_754, E_759, k9_subset_1(A_758, C_757, D_756)) | ~m1_subset_1(F_755, k1_zfmisc_1(k2_zfmisc_1(D_756, B_754))) | ~v1_funct_2(F_755, D_756, B_754) | ~v1_funct_1(F_755) | ~m1_subset_1(E_759, k1_zfmisc_1(k2_zfmisc_1(C_757, B_754))) | ~v1_funct_2(E_759, C_757, B_754) | ~v1_funct_1(E_759) | ~m1_subset_1(D_756, k1_zfmisc_1(A_758)) | v1_xboole_0(D_756) | ~m1_subset_1(C_757, k1_zfmisc_1(A_758)) | v1_xboole_0(C_757) | v1_xboole_0(B_754) | v1_xboole_0(A_758))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.70/2.34  tff(c_3182, plain, (![C_855, A_856, F_851, E_854, D_852, B_853]: (k2_partfun1(k4_subset_1(A_856, C_855, D_852), B_853, k1_tmap_1(A_856, B_853, C_855, D_852, E_854, F_851), C_855)=E_854 | ~v1_funct_2(k1_tmap_1(A_856, B_853, C_855, D_852, E_854, F_851), k4_subset_1(A_856, C_855, D_852), B_853) | ~v1_funct_1(k1_tmap_1(A_856, B_853, C_855, D_852, E_854, F_851)) | k2_partfun1(D_852, B_853, F_851, k9_subset_1(A_856, C_855, D_852))!=k2_partfun1(C_855, B_853, E_854, k9_subset_1(A_856, C_855, D_852)) | ~m1_subset_1(F_851, k1_zfmisc_1(k2_zfmisc_1(D_852, B_853))) | ~v1_funct_2(F_851, D_852, B_853) | ~v1_funct_1(F_851) | ~m1_subset_1(E_854, k1_zfmisc_1(k2_zfmisc_1(C_855, B_853))) | ~v1_funct_2(E_854, C_855, B_853) | ~v1_funct_1(E_854) | ~m1_subset_1(D_852, k1_zfmisc_1(A_856)) | v1_xboole_0(D_852) | ~m1_subset_1(C_855, k1_zfmisc_1(A_856)) | v1_xboole_0(C_855) | v1_xboole_0(B_853) | v1_xboole_0(A_856))), inference(resolution, [status(thm)], [c_36, c_2632])).
% 6.70/2.34  tff(c_3290, plain, (![C_878, F_874, A_879, E_877, D_875, B_876]: (k2_partfun1(k4_subset_1(A_879, C_878, D_875), B_876, k1_tmap_1(A_879, B_876, C_878, D_875, E_877, F_874), C_878)=E_877 | ~v1_funct_1(k1_tmap_1(A_879, B_876, C_878, D_875, E_877, F_874)) | k2_partfun1(D_875, B_876, F_874, k9_subset_1(A_879, C_878, D_875))!=k2_partfun1(C_878, B_876, E_877, k9_subset_1(A_879, C_878, D_875)) | ~m1_subset_1(F_874, k1_zfmisc_1(k2_zfmisc_1(D_875, B_876))) | ~v1_funct_2(F_874, D_875, B_876) | ~v1_funct_1(F_874) | ~m1_subset_1(E_877, k1_zfmisc_1(k2_zfmisc_1(C_878, B_876))) | ~v1_funct_2(E_877, C_878, B_876) | ~v1_funct_1(E_877) | ~m1_subset_1(D_875, k1_zfmisc_1(A_879)) | v1_xboole_0(D_875) | ~m1_subset_1(C_878, k1_zfmisc_1(A_879)) | v1_xboole_0(C_878) | v1_xboole_0(B_876) | v1_xboole_0(A_879))), inference(resolution, [status(thm)], [c_38, c_3182])).
% 6.70/2.34  tff(c_3294, plain, (![A_879, C_878, E_877]: (k2_partfun1(k4_subset_1(A_879, C_878, '#skF_6'), '#skF_4', k1_tmap_1(A_879, '#skF_4', C_878, '#skF_6', E_877, '#skF_8'), C_878)=E_877 | ~v1_funct_1(k1_tmap_1(A_879, '#skF_4', C_878, '#skF_6', E_877, '#skF_8')) | k2_partfun1(C_878, '#skF_4', E_877, k9_subset_1(A_879, C_878, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_879, C_878, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_877, k1_zfmisc_1(k2_zfmisc_1(C_878, '#skF_4'))) | ~v1_funct_2(E_877, C_878, '#skF_4') | ~v1_funct_1(E_877) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_879)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_878, k1_zfmisc_1(A_879)) | v1_xboole_0(C_878) | v1_xboole_0('#skF_4') | v1_xboole_0(A_879))), inference(resolution, [status(thm)], [c_44, c_3290])).
% 6.70/2.34  tff(c_3300, plain, (![A_879, C_878, E_877]: (k2_partfun1(k4_subset_1(A_879, C_878, '#skF_6'), '#skF_4', k1_tmap_1(A_879, '#skF_4', C_878, '#skF_6', E_877, '#skF_8'), C_878)=E_877 | ~v1_funct_1(k1_tmap_1(A_879, '#skF_4', C_878, '#skF_6', E_877, '#skF_8')) | k2_partfun1(C_878, '#skF_4', E_877, k9_subset_1(A_879, C_878, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_879, C_878, '#skF_6')) | ~m1_subset_1(E_877, k1_zfmisc_1(k2_zfmisc_1(C_878, '#skF_4'))) | ~v1_funct_2(E_877, C_878, '#skF_4') | ~v1_funct_1(E_877) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_879)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_878, k1_zfmisc_1(A_879)) | v1_xboole_0(C_878) | v1_xboole_0('#skF_4') | v1_xboole_0(A_879))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2269, c_3294])).
% 6.70/2.34  tff(c_3306, plain, (![A_880, C_881, E_882]: (k2_partfun1(k4_subset_1(A_880, C_881, '#skF_6'), '#skF_4', k1_tmap_1(A_880, '#skF_4', C_881, '#skF_6', E_882, '#skF_8'), C_881)=E_882 | ~v1_funct_1(k1_tmap_1(A_880, '#skF_4', C_881, '#skF_6', E_882, '#skF_8')) | k2_partfun1(C_881, '#skF_4', E_882, k9_subset_1(A_880, C_881, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_880, C_881, '#skF_6')) | ~m1_subset_1(E_882, k1_zfmisc_1(k2_zfmisc_1(C_881, '#skF_4'))) | ~v1_funct_2(E_882, C_881, '#skF_4') | ~v1_funct_1(E_882) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_880)) | ~m1_subset_1(C_881, k1_zfmisc_1(A_880)) | v1_xboole_0(C_881) | v1_xboole_0(A_880))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_3300])).
% 6.70/2.34  tff(c_3313, plain, (![A_880]: (k2_partfun1(k4_subset_1(A_880, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_880, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_880, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_880, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_880, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_880)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_880)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_880))), inference(resolution, [status(thm)], [c_50, c_3306])).
% 6.70/2.34  tff(c_3323, plain, (![A_880]: (k2_partfun1(k4_subset_1(A_880, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_880, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_880, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_880, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_880, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_880)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_880)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_880))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2272, c_3313])).
% 6.70/2.34  tff(c_3325, plain, (![A_883]: (k2_partfun1(k4_subset_1(A_883, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_883, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_883, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_883, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_883, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_883)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_883)) | v1_xboole_0(A_883))), inference(negUnitSimplification, [status(thm)], [c_64, c_3323])).
% 6.70/2.34  tff(c_732, plain, (![A_374, B_375]: (k7_relat_1(A_374, B_375)=k1_xboole_0 | ~r1_xboole_0(B_375, k1_relat_1(A_374)) | ~v1_relat_1(A_374))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.70/2.34  tff(c_785, plain, (![A_381, A_382]: (k7_relat_1(A_381, A_382)=k1_xboole_0 | ~v1_relat_1(A_381) | ~v1_xboole_0(A_382))), inference(resolution, [status(thm)], [c_85, c_732])).
% 6.70/2.34  tff(c_810, plain, (![A_385]: (k7_relat_1('#skF_8', A_385)=k1_xboole_0 | ~v1_xboole_0(A_385))), inference(resolution, [status(thm)], [c_665, c_785])).
% 6.70/2.34  tff(c_814, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_810])).
% 6.70/2.34  tff(c_707, plain, (![A_370, B_371]: (r1_xboole_0(A_370, B_371) | ~r1_subset_1(A_370, B_371) | v1_xboole_0(B_371) | v1_xboole_0(A_370))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.70/2.34  tff(c_877, plain, (![A_400, B_401]: (k3_xboole_0(A_400, B_401)=k1_xboole_0 | ~r1_subset_1(A_400, B_401) | v1_xboole_0(B_401) | v1_xboole_0(A_400))), inference(resolution, [status(thm)], [c_707, c_6])).
% 6.70/2.34  tff(c_883, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_877])).
% 6.70/2.34  tff(c_887, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_60, c_883])).
% 6.70/2.34  tff(c_801, plain, (![A_384]: (k7_relat_1('#skF_7', A_384)=k1_xboole_0 | ~v1_xboole_0(A_384))), inference(resolution, [status(thm)], [c_666, c_785])).
% 6.70/2.34  tff(c_805, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_801])).
% 6.70/2.34  tff(c_753, plain, (![A_376, B_377, C_378]: (k9_subset_1(A_376, B_377, C_378)=k3_xboole_0(B_377, C_378) | ~m1_subset_1(C_378, k1_zfmisc_1(A_376)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.70/2.34  tff(c_765, plain, (![B_377]: (k9_subset_1('#skF_3', B_377, '#skF_6')=k3_xboole_0(B_377, '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_753])).
% 6.70/2.34  tff(c_978, plain, (![F_416, C_420, B_418, A_421, E_419, D_417]: (v1_funct_1(k1_tmap_1(A_421, B_418, C_420, D_417, E_419, F_416)) | ~m1_subset_1(F_416, k1_zfmisc_1(k2_zfmisc_1(D_417, B_418))) | ~v1_funct_2(F_416, D_417, B_418) | ~v1_funct_1(F_416) | ~m1_subset_1(E_419, k1_zfmisc_1(k2_zfmisc_1(C_420, B_418))) | ~v1_funct_2(E_419, C_420, B_418) | ~v1_funct_1(E_419) | ~m1_subset_1(D_417, k1_zfmisc_1(A_421)) | v1_xboole_0(D_417) | ~m1_subset_1(C_420, k1_zfmisc_1(A_421)) | v1_xboole_0(C_420) | v1_xboole_0(B_418) | v1_xboole_0(A_421))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.70/2.34  tff(c_980, plain, (![A_421, C_420, E_419]: (v1_funct_1(k1_tmap_1(A_421, '#skF_4', C_420, '#skF_6', E_419, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_419, k1_zfmisc_1(k2_zfmisc_1(C_420, '#skF_4'))) | ~v1_funct_2(E_419, C_420, '#skF_4') | ~v1_funct_1(E_419) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_421)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_420, k1_zfmisc_1(A_421)) | v1_xboole_0(C_420) | v1_xboole_0('#skF_4') | v1_xboole_0(A_421))), inference(resolution, [status(thm)], [c_44, c_978])).
% 6.70/2.34  tff(c_985, plain, (![A_421, C_420, E_419]: (v1_funct_1(k1_tmap_1(A_421, '#skF_4', C_420, '#skF_6', E_419, '#skF_8')) | ~m1_subset_1(E_419, k1_zfmisc_1(k2_zfmisc_1(C_420, '#skF_4'))) | ~v1_funct_2(E_419, C_420, '#skF_4') | ~v1_funct_1(E_419) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_421)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_420, k1_zfmisc_1(A_421)) | v1_xboole_0(C_420) | v1_xboole_0('#skF_4') | v1_xboole_0(A_421))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_980])).
% 6.70/2.34  tff(c_1294, plain, (![A_492, C_493, E_494]: (v1_funct_1(k1_tmap_1(A_492, '#skF_4', C_493, '#skF_6', E_494, '#skF_8')) | ~m1_subset_1(E_494, k1_zfmisc_1(k2_zfmisc_1(C_493, '#skF_4'))) | ~v1_funct_2(E_494, C_493, '#skF_4') | ~v1_funct_1(E_494) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_492)) | ~m1_subset_1(C_493, k1_zfmisc_1(A_492)) | v1_xboole_0(C_493) | v1_xboole_0(A_492))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_985])).
% 6.70/2.34  tff(c_1301, plain, (![A_492]: (v1_funct_1(k1_tmap_1(A_492, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_492)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_492)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_492))), inference(resolution, [status(thm)], [c_50, c_1294])).
% 6.70/2.34  tff(c_1311, plain, (![A_492]: (v1_funct_1(k1_tmap_1(A_492, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_492)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_492)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_492))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1301])).
% 6.70/2.34  tff(c_1377, plain, (![A_518]: (v1_funct_1(k1_tmap_1(A_518, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_518)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_518)) | v1_xboole_0(A_518))), inference(negUnitSimplification, [status(thm)], [c_64, c_1311])).
% 6.70/2.34  tff(c_1380, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1377])).
% 6.70/2.34  tff(c_1383, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1380])).
% 6.70/2.34  tff(c_1384, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1383])).
% 6.70/2.34  tff(c_888, plain, (![A_402, B_403, C_404, D_405]: (k2_partfun1(A_402, B_403, C_404, D_405)=k7_relat_1(C_404, D_405) | ~m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~v1_funct_1(C_404))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.70/2.34  tff(c_892, plain, (![D_405]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_405)=k7_relat_1('#skF_7', D_405) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_50, c_888])).
% 6.70/2.34  tff(c_898, plain, (![D_405]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_405)=k7_relat_1('#skF_7', D_405))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_892])).
% 6.70/2.34  tff(c_890, plain, (![D_405]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_405)=k7_relat_1('#skF_8', D_405) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_44, c_888])).
% 6.70/2.34  tff(c_895, plain, (![D_405]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_405)=k7_relat_1('#skF_8', D_405))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_890])).
% 6.70/2.34  tff(c_1246, plain, (![E_487, B_482, A_486, D_484, F_483, C_485]: (k2_partfun1(k4_subset_1(A_486, C_485, D_484), B_482, k1_tmap_1(A_486, B_482, C_485, D_484, E_487, F_483), D_484)=F_483 | ~m1_subset_1(k1_tmap_1(A_486, B_482, C_485, D_484, E_487, F_483), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_486, C_485, D_484), B_482))) | ~v1_funct_2(k1_tmap_1(A_486, B_482, C_485, D_484, E_487, F_483), k4_subset_1(A_486, C_485, D_484), B_482) | ~v1_funct_1(k1_tmap_1(A_486, B_482, C_485, D_484, E_487, F_483)) | k2_partfun1(D_484, B_482, F_483, k9_subset_1(A_486, C_485, D_484))!=k2_partfun1(C_485, B_482, E_487, k9_subset_1(A_486, C_485, D_484)) | ~m1_subset_1(F_483, k1_zfmisc_1(k2_zfmisc_1(D_484, B_482))) | ~v1_funct_2(F_483, D_484, B_482) | ~v1_funct_1(F_483) | ~m1_subset_1(E_487, k1_zfmisc_1(k2_zfmisc_1(C_485, B_482))) | ~v1_funct_2(E_487, C_485, B_482) | ~v1_funct_1(E_487) | ~m1_subset_1(D_484, k1_zfmisc_1(A_486)) | v1_xboole_0(D_484) | ~m1_subset_1(C_485, k1_zfmisc_1(A_486)) | v1_xboole_0(C_485) | v1_xboole_0(B_482) | v1_xboole_0(A_486))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.70/2.34  tff(c_1794, plain, (![E_594, C_595, B_593, D_592, F_591, A_596]: (k2_partfun1(k4_subset_1(A_596, C_595, D_592), B_593, k1_tmap_1(A_596, B_593, C_595, D_592, E_594, F_591), D_592)=F_591 | ~v1_funct_2(k1_tmap_1(A_596, B_593, C_595, D_592, E_594, F_591), k4_subset_1(A_596, C_595, D_592), B_593) | ~v1_funct_1(k1_tmap_1(A_596, B_593, C_595, D_592, E_594, F_591)) | k2_partfun1(D_592, B_593, F_591, k9_subset_1(A_596, C_595, D_592))!=k2_partfun1(C_595, B_593, E_594, k9_subset_1(A_596, C_595, D_592)) | ~m1_subset_1(F_591, k1_zfmisc_1(k2_zfmisc_1(D_592, B_593))) | ~v1_funct_2(F_591, D_592, B_593) | ~v1_funct_1(F_591) | ~m1_subset_1(E_594, k1_zfmisc_1(k2_zfmisc_1(C_595, B_593))) | ~v1_funct_2(E_594, C_595, B_593) | ~v1_funct_1(E_594) | ~m1_subset_1(D_592, k1_zfmisc_1(A_596)) | v1_xboole_0(D_592) | ~m1_subset_1(C_595, k1_zfmisc_1(A_596)) | v1_xboole_0(C_595) | v1_xboole_0(B_593) | v1_xboole_0(A_596))), inference(resolution, [status(thm)], [c_36, c_1246])).
% 6.70/2.34  tff(c_1933, plain, (![B_617, D_616, E_618, A_620, F_615, C_619]: (k2_partfun1(k4_subset_1(A_620, C_619, D_616), B_617, k1_tmap_1(A_620, B_617, C_619, D_616, E_618, F_615), D_616)=F_615 | ~v1_funct_1(k1_tmap_1(A_620, B_617, C_619, D_616, E_618, F_615)) | k2_partfun1(D_616, B_617, F_615, k9_subset_1(A_620, C_619, D_616))!=k2_partfun1(C_619, B_617, E_618, k9_subset_1(A_620, C_619, D_616)) | ~m1_subset_1(F_615, k1_zfmisc_1(k2_zfmisc_1(D_616, B_617))) | ~v1_funct_2(F_615, D_616, B_617) | ~v1_funct_1(F_615) | ~m1_subset_1(E_618, k1_zfmisc_1(k2_zfmisc_1(C_619, B_617))) | ~v1_funct_2(E_618, C_619, B_617) | ~v1_funct_1(E_618) | ~m1_subset_1(D_616, k1_zfmisc_1(A_620)) | v1_xboole_0(D_616) | ~m1_subset_1(C_619, k1_zfmisc_1(A_620)) | v1_xboole_0(C_619) | v1_xboole_0(B_617) | v1_xboole_0(A_620))), inference(resolution, [status(thm)], [c_38, c_1794])).
% 6.70/2.34  tff(c_1937, plain, (![A_620, C_619, E_618]: (k2_partfun1(k4_subset_1(A_620, C_619, '#skF_6'), '#skF_4', k1_tmap_1(A_620, '#skF_4', C_619, '#skF_6', E_618, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_620, '#skF_4', C_619, '#skF_6', E_618, '#skF_8')) | k2_partfun1(C_619, '#skF_4', E_618, k9_subset_1(A_620, C_619, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_620, C_619, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_618, k1_zfmisc_1(k2_zfmisc_1(C_619, '#skF_4'))) | ~v1_funct_2(E_618, C_619, '#skF_4') | ~v1_funct_1(E_618) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_620)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_619, k1_zfmisc_1(A_620)) | v1_xboole_0(C_619) | v1_xboole_0('#skF_4') | v1_xboole_0(A_620))), inference(resolution, [status(thm)], [c_44, c_1933])).
% 6.70/2.34  tff(c_1943, plain, (![A_620, C_619, E_618]: (k2_partfun1(k4_subset_1(A_620, C_619, '#skF_6'), '#skF_4', k1_tmap_1(A_620, '#skF_4', C_619, '#skF_6', E_618, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_620, '#skF_4', C_619, '#skF_6', E_618, '#skF_8')) | k2_partfun1(C_619, '#skF_4', E_618, k9_subset_1(A_620, C_619, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_620, C_619, '#skF_6')) | ~m1_subset_1(E_618, k1_zfmisc_1(k2_zfmisc_1(C_619, '#skF_4'))) | ~v1_funct_2(E_618, C_619, '#skF_4') | ~v1_funct_1(E_618) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_620)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_619, k1_zfmisc_1(A_620)) | v1_xboole_0(C_619) | v1_xboole_0('#skF_4') | v1_xboole_0(A_620))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_895, c_1937])).
% 6.70/2.34  tff(c_1949, plain, (![A_621, C_622, E_623]: (k2_partfun1(k4_subset_1(A_621, C_622, '#skF_6'), '#skF_4', k1_tmap_1(A_621, '#skF_4', C_622, '#skF_6', E_623, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_621, '#skF_4', C_622, '#skF_6', E_623, '#skF_8')) | k2_partfun1(C_622, '#skF_4', E_623, k9_subset_1(A_621, C_622, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_621, C_622, '#skF_6')) | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(C_622, '#skF_4'))) | ~v1_funct_2(E_623, C_622, '#skF_4') | ~v1_funct_1(E_623) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_621)) | ~m1_subset_1(C_622, k1_zfmisc_1(A_621)) | v1_xboole_0(C_622) | v1_xboole_0(A_621))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1943])).
% 6.70/2.34  tff(c_1956, plain, (![A_621]: (k2_partfun1(k4_subset_1(A_621, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_621, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_621, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_621, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_621, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_621)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_621)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_621))), inference(resolution, [status(thm)], [c_50, c_1949])).
% 6.70/2.34  tff(c_1966, plain, (![A_621]: (k2_partfun1(k4_subset_1(A_621, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_621, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_621, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_621, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_621, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_621)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_621)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_621))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_898, c_1956])).
% 6.70/2.34  tff(c_1968, plain, (![A_624]: (k2_partfun1(k4_subset_1(A_624, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_624, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_624, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_624, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_624, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_624)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_624)) | v1_xboole_0(A_624))), inference(negUnitSimplification, [status(thm)], [c_64, c_1966])).
% 6.70/2.34  tff(c_103, plain, (![C_231, A_232, B_233]: (v1_relat_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.70/2.34  tff(c_110, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_103])).
% 6.70/2.34  tff(c_164, plain, (![A_246, B_247]: (k7_relat_1(A_246, B_247)=k1_xboole_0 | ~r1_xboole_0(B_247, k1_relat_1(A_246)) | ~v1_relat_1(A_246))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.70/2.34  tff(c_180, plain, (![A_248, A_249]: (k7_relat_1(A_248, A_249)=k1_xboole_0 | ~v1_relat_1(A_248) | ~v1_xboole_0(A_249))), inference(resolution, [status(thm)], [c_85, c_164])).
% 6.70/2.34  tff(c_213, plain, (![A_253]: (k7_relat_1('#skF_8', A_253)=k1_xboole_0 | ~v1_xboole_0(A_253))), inference(resolution, [status(thm)], [c_110, c_180])).
% 6.70/2.34  tff(c_217, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_213])).
% 6.70/2.34  tff(c_187, plain, (![A_250, B_251]: (r1_xboole_0(A_250, B_251) | ~r1_subset_1(A_250, B_251) | v1_xboole_0(B_251) | v1_xboole_0(A_250))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.70/2.34  tff(c_329, plain, (![A_277, B_278]: (k3_xboole_0(A_277, B_278)=k1_xboole_0 | ~r1_subset_1(A_277, B_278) | v1_xboole_0(B_278) | v1_xboole_0(A_277))), inference(resolution, [status(thm)], [c_187, c_6])).
% 6.70/2.34  tff(c_335, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_329])).
% 6.70/2.34  tff(c_339, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_60, c_335])).
% 6.70/2.34  tff(c_111, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_103])).
% 6.70/2.34  tff(c_204, plain, (![A_252]: (k7_relat_1('#skF_7', A_252)=k1_xboole_0 | ~v1_xboole_0(A_252))), inference(resolution, [status(thm)], [c_111, c_180])).
% 6.70/2.34  tff(c_208, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_204])).
% 6.70/2.34  tff(c_262, plain, (![A_265, B_266, C_267, D_268]: (k2_partfun1(A_265, B_266, C_267, D_268)=k7_relat_1(C_267, D_268) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~v1_funct_1(C_267))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.70/2.34  tff(c_266, plain, (![D_268]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_268)=k7_relat_1('#skF_7', D_268) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_50, c_262])).
% 6.70/2.34  tff(c_272, plain, (![D_268]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_268)=k7_relat_1('#skF_7', D_268))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_266])).
% 6.70/2.34  tff(c_264, plain, (![D_268]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_268)=k7_relat_1('#skF_8', D_268) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_44, c_262])).
% 6.70/2.34  tff(c_269, plain, (![D_268]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_268)=k7_relat_1('#skF_8', D_268))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_264])).
% 6.70/2.34  tff(c_249, plain, (![A_262, B_263, C_264]: (k9_subset_1(A_262, B_263, C_264)=k3_xboole_0(B_263, C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(A_262)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.70/2.34  tff(c_261, plain, (![B_263]: (k9_subset_1('#skF_3', B_263, '#skF_6')=k3_xboole_0(B_263, '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_249])).
% 6.70/2.34  tff(c_42, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.70/2.34  tff(c_86, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_42])).
% 6.70/2.34  tff(c_282, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_261, c_86])).
% 6.70/2.34  tff(c_635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_339, c_208, c_339, c_272, c_269, c_282])).
% 6.70/2.34  tff(c_636, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_42])).
% 6.70/2.34  tff(c_681, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_636])).
% 6.70/2.34  tff(c_1979, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1968, c_681])).
% 6.70/2.34  tff(c_1993, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_814, c_887, c_805, c_887, c_765, c_765, c_1384, c_1979])).
% 6.70/2.34  tff(c_1995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1993])).
% 6.70/2.34  tff(c_1996, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_636])).
% 6.70/2.34  tff(c_3334, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3325, c_1996])).
% 6.70/2.34  tff(c_3345, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_2059, c_2198, c_2050, c_2198, c_2137, c_2137, c_2695, c_3334])).
% 6.70/2.34  tff(c_3347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3345])).
% 6.70/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.34  
% 6.70/2.34  Inference rules
% 6.70/2.34  ----------------------
% 6.70/2.34  #Ref     : 0
% 6.70/2.34  #Sup     : 715
% 6.70/2.34  #Fact    : 0
% 6.70/2.34  #Define  : 0
% 6.70/2.34  #Split   : 2
% 6.70/2.34  #Chain   : 0
% 6.70/2.34  #Close   : 0
% 6.70/2.34  
% 6.70/2.34  Ordering : KBO
% 6.70/2.34  
% 6.70/2.34  Simplification rules
% 6.70/2.34  ----------------------
% 6.70/2.34  #Subsume      : 110
% 6.70/2.34  #Demod        : 376
% 6.70/2.34  #Tautology    : 270
% 6.70/2.34  #SimpNegUnit  : 142
% 6.70/2.34  #BackRed      : 4
% 6.70/2.34  
% 6.70/2.34  #Partial instantiations: 0
% 6.70/2.34  #Strategies tried      : 1
% 6.70/2.34  
% 6.70/2.34  Timing (in seconds)
% 6.70/2.34  ----------------------
% 6.70/2.35  Preprocessing        : 0.42
% 6.70/2.35  Parsing              : 0.22
% 6.70/2.35  CNF conversion       : 0.06
% 6.70/2.35  Main loop            : 1.06
% 6.70/2.35  Inferencing          : 0.40
% 6.70/2.35  Reduction            : 0.32
% 6.70/2.35  Demodulation         : 0.23
% 6.70/2.35  BG Simplification    : 0.05
% 6.70/2.35  Subsumption          : 0.22
% 6.70/2.35  Abstraction          : 0.05
% 6.70/2.35  MUC search           : 0.00
% 6.70/2.35  Cooper               : 0.00
% 6.70/2.35  Total                : 1.54
% 6.70/2.35  Index Insertion      : 0.00
% 6.70/2.35  Index Deletion       : 0.00
% 6.70/2.35  Index Matching       : 0.00
% 6.70/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
