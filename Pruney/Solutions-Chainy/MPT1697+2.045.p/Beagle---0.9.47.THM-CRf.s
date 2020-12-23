%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:16 EST 2020

% Result     : Theorem 14.16s
% Output     : CNFRefutation 14.23s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 459 expanded)
%              Number of leaves         :   45 ( 189 expanded)
%              Depth                    :   12
%              Number of atoms          :  604 (2566 expanded)
%              Number of equality atoms :  105 ( 452 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_269,negated_conjecture,(
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

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_227,axiom,(
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

tff(f_145,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_193,axiom,(
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

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_88,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_84,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_951,plain,(
    ! [C_380,A_381,B_382] :
      ( v1_relat_1(C_380)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_964,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_951])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_11656,plain,(
    ! [A_1611,B_1612,C_1613] :
      ( ~ r1_xboole_0(A_1611,B_1612)
      | ~ r2_hidden(C_1613,B_1612)
      | ~ r2_hidden(C_1613,A_1611) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_11666,plain,(
    ! [C_1614] : ~ r2_hidden(C_1614,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_11656])).

tff(c_11676,plain,(
    ! [B_4] : r1_xboole_0(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_10,c_11666])).

tff(c_11868,plain,(
    ! [A_1640,B_1641] :
      ( k7_relat_1(A_1640,B_1641) = k1_xboole_0
      | ~ r1_xboole_0(B_1641,k1_relat_1(A_1640))
      | ~ v1_relat_1(A_1640) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11889,plain,(
    ! [A_1642] :
      ( k7_relat_1(A_1642,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_1642) ) ),
    inference(resolution,[status(thm)],[c_11676,c_11868])).

tff(c_11900,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_964,c_11889])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_963,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_951])).

tff(c_11901,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_963,c_11889])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_82,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_12001,plain,(
    ! [A_1658,B_1659] :
      ( r1_xboole_0(A_1658,B_1659)
      | ~ r1_subset_1(A_1658,B_1659)
      | v1_xboole_0(B_1659)
      | v1_xboole_0(A_1658) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_13077,plain,(
    ! [A_1775,B_1776] :
      ( k3_xboole_0(A_1775,B_1776) = k1_xboole_0
      | ~ r1_subset_1(A_1775,B_1776)
      | v1_xboole_0(B_1776)
      | v1_xboole_0(A_1775) ) ),
    inference(resolution,[status(thm)],[c_12001,c_2])).

tff(c_13080,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_13077])).

tff(c_13083,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_13080])).

tff(c_12067,plain,(
    ! [A_1667,B_1668,C_1669] :
      ( k9_subset_1(A_1667,B_1668,C_1669) = k3_xboole_0(B_1668,C_1669)
      | ~ m1_subset_1(C_1669,k1_zfmisc_1(A_1667)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12082,plain,(
    ! [B_1668] : k9_subset_1('#skF_2',B_1668,'#skF_5') = k3_xboole_0(B_1668,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_12067])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_72,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_13187,plain,(
    ! [D_1789,F_1790,A_1792,C_1791,E_1793,B_1794] :
      ( v1_funct_1(k1_tmap_1(A_1792,B_1794,C_1791,D_1789,E_1793,F_1790))
      | ~ m1_subset_1(F_1790,k1_zfmisc_1(k2_zfmisc_1(D_1789,B_1794)))
      | ~ v1_funct_2(F_1790,D_1789,B_1794)
      | ~ v1_funct_1(F_1790)
      | ~ m1_subset_1(E_1793,k1_zfmisc_1(k2_zfmisc_1(C_1791,B_1794)))
      | ~ v1_funct_2(E_1793,C_1791,B_1794)
      | ~ v1_funct_1(E_1793)
      | ~ m1_subset_1(D_1789,k1_zfmisc_1(A_1792))
      | v1_xboole_0(D_1789)
      | ~ m1_subset_1(C_1791,k1_zfmisc_1(A_1792))
      | v1_xboole_0(C_1791)
      | v1_xboole_0(B_1794)
      | v1_xboole_0(A_1792) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_13192,plain,(
    ! [A_1792,C_1791,E_1793] :
      ( v1_funct_1(k1_tmap_1(A_1792,'#skF_3',C_1791,'#skF_5',E_1793,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1793,k1_zfmisc_1(k2_zfmisc_1(C_1791,'#skF_3')))
      | ~ v1_funct_2(E_1793,C_1791,'#skF_3')
      | ~ v1_funct_1(E_1793)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1792))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1791,k1_zfmisc_1(A_1792))
      | v1_xboole_0(C_1791)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1792) ) ),
    inference(resolution,[status(thm)],[c_70,c_13187])).

tff(c_13198,plain,(
    ! [A_1792,C_1791,E_1793] :
      ( v1_funct_1(k1_tmap_1(A_1792,'#skF_3',C_1791,'#skF_5',E_1793,'#skF_7'))
      | ~ m1_subset_1(E_1793,k1_zfmisc_1(k2_zfmisc_1(C_1791,'#skF_3')))
      | ~ v1_funct_2(E_1793,C_1791,'#skF_3')
      | ~ v1_funct_1(E_1793)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1792))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1791,k1_zfmisc_1(A_1792))
      | v1_xboole_0(C_1791)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1792) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_13192])).

tff(c_13748,plain,(
    ! [A_1869,C_1870,E_1871] :
      ( v1_funct_1(k1_tmap_1(A_1869,'#skF_3',C_1870,'#skF_5',E_1871,'#skF_7'))
      | ~ m1_subset_1(E_1871,k1_zfmisc_1(k2_zfmisc_1(C_1870,'#skF_3')))
      | ~ v1_funct_2(E_1871,C_1870,'#skF_3')
      | ~ v1_funct_1(E_1871)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1869))
      | ~ m1_subset_1(C_1870,k1_zfmisc_1(A_1869))
      | v1_xboole_0(C_1870)
      | v1_xboole_0(A_1869) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_13198])).

tff(c_13758,plain,(
    ! [A_1869] :
      ( v1_funct_1(k1_tmap_1(A_1869,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1869))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1869))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1869) ) ),
    inference(resolution,[status(thm)],[c_76,c_13748])).

tff(c_13769,plain,(
    ! [A_1869] :
      ( v1_funct_1(k1_tmap_1(A_1869,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1869))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1869))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1869) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_13758])).

tff(c_13964,plain,(
    ! [A_1903] :
      ( v1_funct_1(k1_tmap_1(A_1903,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1903))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1903))
      | v1_xboole_0(A_1903) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_13769])).

tff(c_13971,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_13964])).

tff(c_13975,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_13971])).

tff(c_13976,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_13975])).

tff(c_13029,plain,(
    ! [A_1766,B_1767,C_1768,D_1769] :
      ( k2_partfun1(A_1766,B_1767,C_1768,D_1769) = k7_relat_1(C_1768,D_1769)
      | ~ m1_subset_1(C_1768,k1_zfmisc_1(k2_zfmisc_1(A_1766,B_1767)))
      | ~ v1_funct_1(C_1768) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_13036,plain,(
    ! [D_1769] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_1769) = k7_relat_1('#skF_6',D_1769)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_13029])).

tff(c_13043,plain,(
    ! [D_1769] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_1769) = k7_relat_1('#skF_6',D_1769) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13036])).

tff(c_13034,plain,(
    ! [D_1769] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_1769) = k7_relat_1('#skF_7',D_1769)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_13029])).

tff(c_13040,plain,(
    ! [D_1769] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_1769) = k7_relat_1('#skF_7',D_1769) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_13034])).

tff(c_64,plain,(
    ! [B_172,A_171,C_173,E_175,F_176,D_174] :
      ( v1_funct_2(k1_tmap_1(A_171,B_172,C_173,D_174,E_175,F_176),k4_subset_1(A_171,C_173,D_174),B_172)
      | ~ m1_subset_1(F_176,k1_zfmisc_1(k2_zfmisc_1(D_174,B_172)))
      | ~ v1_funct_2(F_176,D_174,B_172)
      | ~ v1_funct_1(F_176)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(C_173,B_172)))
      | ~ v1_funct_2(E_175,C_173,B_172)
      | ~ v1_funct_1(E_175)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(A_171))
      | v1_xboole_0(D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_171))
      | v1_xboole_0(C_173)
      | v1_xboole_0(B_172)
      | v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_62,plain,(
    ! [B_172,A_171,C_173,E_175,F_176,D_174] :
      ( m1_subset_1(k1_tmap_1(A_171,B_172,C_173,D_174,E_175,F_176),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_171,C_173,D_174),B_172)))
      | ~ m1_subset_1(F_176,k1_zfmisc_1(k2_zfmisc_1(D_174,B_172)))
      | ~ v1_funct_2(F_176,D_174,B_172)
      | ~ v1_funct_1(F_176)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(C_173,B_172)))
      | ~ v1_funct_2(E_175,C_173,B_172)
      | ~ v1_funct_1(E_175)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(A_171))
      | v1_xboole_0(D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_171))
      | v1_xboole_0(C_173)
      | v1_xboole_0(B_172)
      | v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_13536,plain,(
    ! [D_1845,C_1844,E_1842,A_1843,F_1840,B_1841] :
      ( k2_partfun1(k4_subset_1(A_1843,C_1844,D_1845),B_1841,k1_tmap_1(A_1843,B_1841,C_1844,D_1845,E_1842,F_1840),C_1844) = E_1842
      | ~ m1_subset_1(k1_tmap_1(A_1843,B_1841,C_1844,D_1845,E_1842,F_1840),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1843,C_1844,D_1845),B_1841)))
      | ~ v1_funct_2(k1_tmap_1(A_1843,B_1841,C_1844,D_1845,E_1842,F_1840),k4_subset_1(A_1843,C_1844,D_1845),B_1841)
      | ~ v1_funct_1(k1_tmap_1(A_1843,B_1841,C_1844,D_1845,E_1842,F_1840))
      | k2_partfun1(D_1845,B_1841,F_1840,k9_subset_1(A_1843,C_1844,D_1845)) != k2_partfun1(C_1844,B_1841,E_1842,k9_subset_1(A_1843,C_1844,D_1845))
      | ~ m1_subset_1(F_1840,k1_zfmisc_1(k2_zfmisc_1(D_1845,B_1841)))
      | ~ v1_funct_2(F_1840,D_1845,B_1841)
      | ~ v1_funct_1(F_1840)
      | ~ m1_subset_1(E_1842,k1_zfmisc_1(k2_zfmisc_1(C_1844,B_1841)))
      | ~ v1_funct_2(E_1842,C_1844,B_1841)
      | ~ v1_funct_1(E_1842)
      | ~ m1_subset_1(D_1845,k1_zfmisc_1(A_1843))
      | v1_xboole_0(D_1845)
      | ~ m1_subset_1(C_1844,k1_zfmisc_1(A_1843))
      | v1_xboole_0(C_1844)
      | v1_xboole_0(B_1841)
      | v1_xboole_0(A_1843) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_15252,plain,(
    ! [F_2063,A_2065,B_2067,E_2066,D_2062,C_2064] :
      ( k2_partfun1(k4_subset_1(A_2065,C_2064,D_2062),B_2067,k1_tmap_1(A_2065,B_2067,C_2064,D_2062,E_2066,F_2063),C_2064) = E_2066
      | ~ v1_funct_2(k1_tmap_1(A_2065,B_2067,C_2064,D_2062,E_2066,F_2063),k4_subset_1(A_2065,C_2064,D_2062),B_2067)
      | ~ v1_funct_1(k1_tmap_1(A_2065,B_2067,C_2064,D_2062,E_2066,F_2063))
      | k2_partfun1(D_2062,B_2067,F_2063,k9_subset_1(A_2065,C_2064,D_2062)) != k2_partfun1(C_2064,B_2067,E_2066,k9_subset_1(A_2065,C_2064,D_2062))
      | ~ m1_subset_1(F_2063,k1_zfmisc_1(k2_zfmisc_1(D_2062,B_2067)))
      | ~ v1_funct_2(F_2063,D_2062,B_2067)
      | ~ v1_funct_1(F_2063)
      | ~ m1_subset_1(E_2066,k1_zfmisc_1(k2_zfmisc_1(C_2064,B_2067)))
      | ~ v1_funct_2(E_2066,C_2064,B_2067)
      | ~ v1_funct_1(E_2066)
      | ~ m1_subset_1(D_2062,k1_zfmisc_1(A_2065))
      | v1_xboole_0(D_2062)
      | ~ m1_subset_1(C_2064,k1_zfmisc_1(A_2065))
      | v1_xboole_0(C_2064)
      | v1_xboole_0(B_2067)
      | v1_xboole_0(A_2065) ) ),
    inference(resolution,[status(thm)],[c_62,c_13536])).

tff(c_21460,plain,(
    ! [A_2714,D_2711,B_2716,E_2715,C_2713,F_2712] :
      ( k2_partfun1(k4_subset_1(A_2714,C_2713,D_2711),B_2716,k1_tmap_1(A_2714,B_2716,C_2713,D_2711,E_2715,F_2712),C_2713) = E_2715
      | ~ v1_funct_1(k1_tmap_1(A_2714,B_2716,C_2713,D_2711,E_2715,F_2712))
      | k2_partfun1(D_2711,B_2716,F_2712,k9_subset_1(A_2714,C_2713,D_2711)) != k2_partfun1(C_2713,B_2716,E_2715,k9_subset_1(A_2714,C_2713,D_2711))
      | ~ m1_subset_1(F_2712,k1_zfmisc_1(k2_zfmisc_1(D_2711,B_2716)))
      | ~ v1_funct_2(F_2712,D_2711,B_2716)
      | ~ v1_funct_1(F_2712)
      | ~ m1_subset_1(E_2715,k1_zfmisc_1(k2_zfmisc_1(C_2713,B_2716)))
      | ~ v1_funct_2(E_2715,C_2713,B_2716)
      | ~ v1_funct_1(E_2715)
      | ~ m1_subset_1(D_2711,k1_zfmisc_1(A_2714))
      | v1_xboole_0(D_2711)
      | ~ m1_subset_1(C_2713,k1_zfmisc_1(A_2714))
      | v1_xboole_0(C_2713)
      | v1_xboole_0(B_2716)
      | v1_xboole_0(A_2714) ) ),
    inference(resolution,[status(thm)],[c_64,c_15252])).

tff(c_21467,plain,(
    ! [A_2714,C_2713,E_2715] :
      ( k2_partfun1(k4_subset_1(A_2714,C_2713,'#skF_5'),'#skF_3',k1_tmap_1(A_2714,'#skF_3',C_2713,'#skF_5',E_2715,'#skF_7'),C_2713) = E_2715
      | ~ v1_funct_1(k1_tmap_1(A_2714,'#skF_3',C_2713,'#skF_5',E_2715,'#skF_7'))
      | k2_partfun1(C_2713,'#skF_3',E_2715,k9_subset_1(A_2714,C_2713,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_2714,C_2713,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2715,k1_zfmisc_1(k2_zfmisc_1(C_2713,'#skF_3')))
      | ~ v1_funct_2(E_2715,C_2713,'#skF_3')
      | ~ v1_funct_1(E_2715)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2714))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2713,k1_zfmisc_1(A_2714))
      | v1_xboole_0(C_2713)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2714) ) ),
    inference(resolution,[status(thm)],[c_70,c_21460])).

tff(c_21474,plain,(
    ! [A_2714,C_2713,E_2715] :
      ( k2_partfun1(k4_subset_1(A_2714,C_2713,'#skF_5'),'#skF_3',k1_tmap_1(A_2714,'#skF_3',C_2713,'#skF_5',E_2715,'#skF_7'),C_2713) = E_2715
      | ~ v1_funct_1(k1_tmap_1(A_2714,'#skF_3',C_2713,'#skF_5',E_2715,'#skF_7'))
      | k2_partfun1(C_2713,'#skF_3',E_2715,k9_subset_1(A_2714,C_2713,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2714,C_2713,'#skF_5'))
      | ~ m1_subset_1(E_2715,k1_zfmisc_1(k2_zfmisc_1(C_2713,'#skF_3')))
      | ~ v1_funct_2(E_2715,C_2713,'#skF_3')
      | ~ v1_funct_1(E_2715)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2714))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2713,k1_zfmisc_1(A_2714))
      | v1_xboole_0(C_2713)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2714) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_13040,c_21467])).

tff(c_22195,plain,(
    ! [A_2770,C_2771,E_2772] :
      ( k2_partfun1(k4_subset_1(A_2770,C_2771,'#skF_5'),'#skF_3',k1_tmap_1(A_2770,'#skF_3',C_2771,'#skF_5',E_2772,'#skF_7'),C_2771) = E_2772
      | ~ v1_funct_1(k1_tmap_1(A_2770,'#skF_3',C_2771,'#skF_5',E_2772,'#skF_7'))
      | k2_partfun1(C_2771,'#skF_3',E_2772,k9_subset_1(A_2770,C_2771,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2770,C_2771,'#skF_5'))
      | ~ m1_subset_1(E_2772,k1_zfmisc_1(k2_zfmisc_1(C_2771,'#skF_3')))
      | ~ v1_funct_2(E_2772,C_2771,'#skF_3')
      | ~ v1_funct_1(E_2772)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2770))
      | ~ m1_subset_1(C_2771,k1_zfmisc_1(A_2770))
      | v1_xboole_0(C_2771)
      | v1_xboole_0(A_2770) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_21474])).

tff(c_22205,plain,(
    ! [A_2770] :
      ( k2_partfun1(k4_subset_1(A_2770,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2770,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2770,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_2770,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2770,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2770))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2770))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2770) ) ),
    inference(resolution,[status(thm)],[c_76,c_22195])).

tff(c_22216,plain,(
    ! [A_2770] :
      ( k2_partfun1(k4_subset_1(A_2770,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2770,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2770,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2770,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2770,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2770))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2770))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2770) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_13043,c_22205])).

tff(c_22218,plain,(
    ! [A_2773] :
      ( k2_partfun1(k4_subset_1(A_2773,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2773,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2773,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2773,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2773,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2773))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2773))
      | v1_xboole_0(A_2773) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_22216])).

tff(c_1063,plain,(
    ! [A_407,B_408,C_409] :
      ( ~ r1_xboole_0(A_407,B_408)
      | ~ r2_hidden(C_409,B_408)
      | ~ r2_hidden(C_409,A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1070,plain,(
    ! [C_410] : ~ r2_hidden(C_410,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_1063])).

tff(c_1080,plain,(
    ! [B_4] : r1_xboole_0(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_10,c_1070])).

tff(c_1334,plain,(
    ! [A_450,B_451] :
      ( k7_relat_1(A_450,B_451) = k1_xboole_0
      | ~ r1_xboole_0(B_451,k1_relat_1(A_450))
      | ~ v1_relat_1(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1360,plain,(
    ! [A_452] :
      ( k7_relat_1(A_452,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_452) ) ),
    inference(resolution,[status(thm)],[c_1080,c_1334])).

tff(c_1371,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_964,c_1360])).

tff(c_1372,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_963,c_1360])).

tff(c_1237,plain,(
    ! [A_432,B_433] :
      ( r1_xboole_0(A_432,B_433)
      | ~ r1_subset_1(A_432,B_433)
      | v1_xboole_0(B_433)
      | v1_xboole_0(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2245,plain,(
    ! [A_569,B_570] :
      ( k3_xboole_0(A_569,B_570) = k1_xboole_0
      | ~ r1_subset_1(A_569,B_570)
      | v1_xboole_0(B_570)
      | v1_xboole_0(A_569) ) ),
    inference(resolution,[status(thm)],[c_1237,c_2])).

tff(c_2248,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_2245])).

tff(c_2251,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_2248])).

tff(c_1505,plain,(
    ! [A_471,B_472,C_473] :
      ( k9_subset_1(A_471,B_472,C_473) = k3_xboole_0(B_472,C_473)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(A_471)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1520,plain,(
    ! [B_472] : k9_subset_1('#skF_2',B_472,'#skF_5') = k3_xboole_0(B_472,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_1505])).

tff(c_2371,plain,(
    ! [C_584,B_587,E_586,D_582,F_583,A_585] :
      ( v1_funct_1(k1_tmap_1(A_585,B_587,C_584,D_582,E_586,F_583))
      | ~ m1_subset_1(F_583,k1_zfmisc_1(k2_zfmisc_1(D_582,B_587)))
      | ~ v1_funct_2(F_583,D_582,B_587)
      | ~ v1_funct_1(F_583)
      | ~ m1_subset_1(E_586,k1_zfmisc_1(k2_zfmisc_1(C_584,B_587)))
      | ~ v1_funct_2(E_586,C_584,B_587)
      | ~ v1_funct_1(E_586)
      | ~ m1_subset_1(D_582,k1_zfmisc_1(A_585))
      | v1_xboole_0(D_582)
      | ~ m1_subset_1(C_584,k1_zfmisc_1(A_585))
      | v1_xboole_0(C_584)
      | v1_xboole_0(B_587)
      | v1_xboole_0(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_2376,plain,(
    ! [A_585,C_584,E_586] :
      ( v1_funct_1(k1_tmap_1(A_585,'#skF_3',C_584,'#skF_5',E_586,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_586,k1_zfmisc_1(k2_zfmisc_1(C_584,'#skF_3')))
      | ~ v1_funct_2(E_586,C_584,'#skF_3')
      | ~ v1_funct_1(E_586)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_585))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_584,k1_zfmisc_1(A_585))
      | v1_xboole_0(C_584)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_585) ) ),
    inference(resolution,[status(thm)],[c_70,c_2371])).

tff(c_2382,plain,(
    ! [A_585,C_584,E_586] :
      ( v1_funct_1(k1_tmap_1(A_585,'#skF_3',C_584,'#skF_5',E_586,'#skF_7'))
      | ~ m1_subset_1(E_586,k1_zfmisc_1(k2_zfmisc_1(C_584,'#skF_3')))
      | ~ v1_funct_2(E_586,C_584,'#skF_3')
      | ~ v1_funct_1(E_586)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_585))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_584,k1_zfmisc_1(A_585))
      | v1_xboole_0(C_584)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_585) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2376])).

tff(c_2449,plain,(
    ! [A_591,C_592,E_593] :
      ( v1_funct_1(k1_tmap_1(A_591,'#skF_3',C_592,'#skF_5',E_593,'#skF_7'))
      | ~ m1_subset_1(E_593,k1_zfmisc_1(k2_zfmisc_1(C_592,'#skF_3')))
      | ~ v1_funct_2(E_593,C_592,'#skF_3')
      | ~ v1_funct_1(E_593)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_591))
      | ~ m1_subset_1(C_592,k1_zfmisc_1(A_591))
      | v1_xboole_0(C_592)
      | v1_xboole_0(A_591) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_2382])).

tff(c_2456,plain,(
    ! [A_591] :
      ( v1_funct_1(k1_tmap_1(A_591,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_591))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_591))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_591) ) ),
    inference(resolution,[status(thm)],[c_76,c_2449])).

tff(c_2464,plain,(
    ! [A_591] :
      ( v1_funct_1(k1_tmap_1(A_591,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_591))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_591))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_591) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2456])).

tff(c_2677,plain,(
    ! [A_628] :
      ( v1_funct_1(k1_tmap_1(A_628,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_628))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_628))
      | v1_xboole_0(A_628) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2464])).

tff(c_2684,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_2677])).

tff(c_2688,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2684])).

tff(c_2689,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2688])).

tff(c_2119,plain,(
    ! [A_551,B_552,C_553,D_554] :
      ( k2_partfun1(A_551,B_552,C_553,D_554) = k7_relat_1(C_553,D_554)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(k2_zfmisc_1(A_551,B_552)))
      | ~ v1_funct_1(C_553) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2126,plain,(
    ! [D_554] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_554) = k7_relat_1('#skF_6',D_554)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_2119])).

tff(c_2133,plain,(
    ! [D_554] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_554) = k7_relat_1('#skF_6',D_554) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2126])).

tff(c_2124,plain,(
    ! [D_554] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_554) = k7_relat_1('#skF_7',D_554)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_2119])).

tff(c_2130,plain,(
    ! [D_554] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_554) = k7_relat_1('#skF_7',D_554) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2124])).

tff(c_2736,plain,(
    ! [F_639,D_644,E_641,B_640,A_642,C_643] :
      ( k2_partfun1(k4_subset_1(A_642,C_643,D_644),B_640,k1_tmap_1(A_642,B_640,C_643,D_644,E_641,F_639),D_644) = F_639
      | ~ m1_subset_1(k1_tmap_1(A_642,B_640,C_643,D_644,E_641,F_639),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_642,C_643,D_644),B_640)))
      | ~ v1_funct_2(k1_tmap_1(A_642,B_640,C_643,D_644,E_641,F_639),k4_subset_1(A_642,C_643,D_644),B_640)
      | ~ v1_funct_1(k1_tmap_1(A_642,B_640,C_643,D_644,E_641,F_639))
      | k2_partfun1(D_644,B_640,F_639,k9_subset_1(A_642,C_643,D_644)) != k2_partfun1(C_643,B_640,E_641,k9_subset_1(A_642,C_643,D_644))
      | ~ m1_subset_1(F_639,k1_zfmisc_1(k2_zfmisc_1(D_644,B_640)))
      | ~ v1_funct_2(F_639,D_644,B_640)
      | ~ v1_funct_1(F_639)
      | ~ m1_subset_1(E_641,k1_zfmisc_1(k2_zfmisc_1(C_643,B_640)))
      | ~ v1_funct_2(E_641,C_643,B_640)
      | ~ v1_funct_1(E_641)
      | ~ m1_subset_1(D_644,k1_zfmisc_1(A_642))
      | v1_xboole_0(D_644)
      | ~ m1_subset_1(C_643,k1_zfmisc_1(A_642))
      | v1_xboole_0(C_643)
      | v1_xboole_0(B_640)
      | v1_xboole_0(A_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_4465,plain,(
    ! [D_869,A_872,B_874,E_873,F_870,C_871] :
      ( k2_partfun1(k4_subset_1(A_872,C_871,D_869),B_874,k1_tmap_1(A_872,B_874,C_871,D_869,E_873,F_870),D_869) = F_870
      | ~ v1_funct_2(k1_tmap_1(A_872,B_874,C_871,D_869,E_873,F_870),k4_subset_1(A_872,C_871,D_869),B_874)
      | ~ v1_funct_1(k1_tmap_1(A_872,B_874,C_871,D_869,E_873,F_870))
      | k2_partfun1(D_869,B_874,F_870,k9_subset_1(A_872,C_871,D_869)) != k2_partfun1(C_871,B_874,E_873,k9_subset_1(A_872,C_871,D_869))
      | ~ m1_subset_1(F_870,k1_zfmisc_1(k2_zfmisc_1(D_869,B_874)))
      | ~ v1_funct_2(F_870,D_869,B_874)
      | ~ v1_funct_1(F_870)
      | ~ m1_subset_1(E_873,k1_zfmisc_1(k2_zfmisc_1(C_871,B_874)))
      | ~ v1_funct_2(E_873,C_871,B_874)
      | ~ v1_funct_1(E_873)
      | ~ m1_subset_1(D_869,k1_zfmisc_1(A_872))
      | v1_xboole_0(D_869)
      | ~ m1_subset_1(C_871,k1_zfmisc_1(A_872))
      | v1_xboole_0(C_871)
      | v1_xboole_0(B_874)
      | v1_xboole_0(A_872) ) ),
    inference(resolution,[status(thm)],[c_62,c_2736])).

tff(c_10552,plain,(
    ! [A_1505,D_1502,E_1506,C_1504,F_1503,B_1507] :
      ( k2_partfun1(k4_subset_1(A_1505,C_1504,D_1502),B_1507,k1_tmap_1(A_1505,B_1507,C_1504,D_1502,E_1506,F_1503),D_1502) = F_1503
      | ~ v1_funct_1(k1_tmap_1(A_1505,B_1507,C_1504,D_1502,E_1506,F_1503))
      | k2_partfun1(D_1502,B_1507,F_1503,k9_subset_1(A_1505,C_1504,D_1502)) != k2_partfun1(C_1504,B_1507,E_1506,k9_subset_1(A_1505,C_1504,D_1502))
      | ~ m1_subset_1(F_1503,k1_zfmisc_1(k2_zfmisc_1(D_1502,B_1507)))
      | ~ v1_funct_2(F_1503,D_1502,B_1507)
      | ~ v1_funct_1(F_1503)
      | ~ m1_subset_1(E_1506,k1_zfmisc_1(k2_zfmisc_1(C_1504,B_1507)))
      | ~ v1_funct_2(E_1506,C_1504,B_1507)
      | ~ v1_funct_1(E_1506)
      | ~ m1_subset_1(D_1502,k1_zfmisc_1(A_1505))
      | v1_xboole_0(D_1502)
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(A_1505))
      | v1_xboole_0(C_1504)
      | v1_xboole_0(B_1507)
      | v1_xboole_0(A_1505) ) ),
    inference(resolution,[status(thm)],[c_64,c_4465])).

tff(c_10559,plain,(
    ! [A_1505,C_1504,E_1506] :
      ( k2_partfun1(k4_subset_1(A_1505,C_1504,'#skF_5'),'#skF_3',k1_tmap_1(A_1505,'#skF_3',C_1504,'#skF_5',E_1506,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1505,'#skF_3',C_1504,'#skF_5',E_1506,'#skF_7'))
      | k2_partfun1(C_1504,'#skF_3',E_1506,k9_subset_1(A_1505,C_1504,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1505,C_1504,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1506,k1_zfmisc_1(k2_zfmisc_1(C_1504,'#skF_3')))
      | ~ v1_funct_2(E_1506,C_1504,'#skF_3')
      | ~ v1_funct_1(E_1506)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1505))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(A_1505))
      | v1_xboole_0(C_1504)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1505) ) ),
    inference(resolution,[status(thm)],[c_70,c_10552])).

tff(c_10566,plain,(
    ! [A_1505,C_1504,E_1506] :
      ( k2_partfun1(k4_subset_1(A_1505,C_1504,'#skF_5'),'#skF_3',k1_tmap_1(A_1505,'#skF_3',C_1504,'#skF_5',E_1506,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1505,'#skF_3',C_1504,'#skF_5',E_1506,'#skF_7'))
      | k2_partfun1(C_1504,'#skF_3',E_1506,k9_subset_1(A_1505,C_1504,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1505,C_1504,'#skF_5'))
      | ~ m1_subset_1(E_1506,k1_zfmisc_1(k2_zfmisc_1(C_1504,'#skF_3')))
      | ~ v1_funct_2(E_1506,C_1504,'#skF_3')
      | ~ v1_funct_1(E_1506)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1505))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(A_1505))
      | v1_xboole_0(C_1504)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1505) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2130,c_10559])).

tff(c_11453,plain,(
    ! [A_1578,C_1579,E_1580] :
      ( k2_partfun1(k4_subset_1(A_1578,C_1579,'#skF_5'),'#skF_3',k1_tmap_1(A_1578,'#skF_3',C_1579,'#skF_5',E_1580,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1578,'#skF_3',C_1579,'#skF_5',E_1580,'#skF_7'))
      | k2_partfun1(C_1579,'#skF_3',E_1580,k9_subset_1(A_1578,C_1579,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1578,C_1579,'#skF_5'))
      | ~ m1_subset_1(E_1580,k1_zfmisc_1(k2_zfmisc_1(C_1579,'#skF_3')))
      | ~ v1_funct_2(E_1580,C_1579,'#skF_3')
      | ~ v1_funct_1(E_1580)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1578))
      | ~ m1_subset_1(C_1579,k1_zfmisc_1(A_1578))
      | v1_xboole_0(C_1579)
      | v1_xboole_0(A_1578) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_10566])).

tff(c_11463,plain,(
    ! [A_1578] :
      ( k2_partfun1(k4_subset_1(A_1578,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1578,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1578,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1578,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1578,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1578))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1578))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1578) ) ),
    inference(resolution,[status(thm)],[c_76,c_11453])).

tff(c_11474,plain,(
    ! [A_1578] :
      ( k2_partfun1(k4_subset_1(A_1578,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1578,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1578,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1578,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1578,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1578))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1578))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2133,c_11463])).

tff(c_11476,plain,(
    ! [A_1581] :
      ( k2_partfun1(k4_subset_1(A_1581,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1581,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1581,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1581,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1581,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1581))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1581))
      | v1_xboole_0(A_1581) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_11474])).

tff(c_183,plain,(
    ! [C_253,A_254,B_255] :
      ( v1_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_195,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_183])).

tff(c_404,plain,(
    ! [A_296,B_297,C_298] :
      ( ~ r1_xboole_0(A_296,B_297)
      | ~ r2_hidden(C_298,B_297)
      | ~ r2_hidden(C_298,A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_417,plain,(
    ! [C_299] : ~ r2_hidden(C_299,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_404])).

tff(c_427,plain,(
    ! [B_4] : r1_xboole_0(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_10,c_417])).

tff(c_495,plain,(
    ! [A_304,B_305] :
      ( k7_relat_1(A_304,B_305) = k1_xboole_0
      | ~ r1_xboole_0(B_305,k1_relat_1(A_304))
      | ~ v1_relat_1(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_516,plain,(
    ! [A_306] :
      ( k7_relat_1(A_306,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_306) ) ),
    inference(resolution,[status(thm)],[c_427,c_495])).

tff(c_528,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_195,c_516])).

tff(c_196,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_183])).

tff(c_527,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_516])).

tff(c_574,plain,(
    ! [A_320,B_321] :
      ( r1_xboole_0(A_320,B_321)
      | ~ r1_subset_1(A_320,B_321)
      | v1_xboole_0(B_321)
      | v1_xboole_0(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_900,plain,(
    ! [A_371,B_372] :
      ( k3_xboole_0(A_371,B_372) = k1_xboole_0
      | ~ r1_subset_1(A_371,B_372)
      | v1_xboole_0(B_372)
      | v1_xboole_0(A_371) ) ),
    inference(resolution,[status(thm)],[c_574,c_2])).

tff(c_903,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_900])).

tff(c_906,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_903])).

tff(c_866,plain,(
    ! [A_365,B_366,C_367,D_368] :
      ( k2_partfun1(A_365,B_366,C_367,D_368) = k7_relat_1(C_367,D_368)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(A_365,B_366)))
      | ~ v1_funct_1(C_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_873,plain,(
    ! [D_368] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_368) = k7_relat_1('#skF_6',D_368)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_866])).

tff(c_880,plain,(
    ! [D_368] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_368) = k7_relat_1('#skF_6',D_368) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_873])).

tff(c_871,plain,(
    ! [D_368] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_368) = k7_relat_1('#skF_7',D_368)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_866])).

tff(c_877,plain,(
    ! [D_368] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_368) = k7_relat_1('#skF_7',D_368) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_871])).

tff(c_750,plain,(
    ! [A_345,B_346,C_347] :
      ( k9_subset_1(A_345,B_346,C_347) = k3_xboole_0(B_346,C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(A_345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_765,plain,(
    ! [B_346] : k9_subset_1('#skF_2',B_346,'#skF_5') = k3_xboole_0(B_346,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_750])).

tff(c_68,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_125,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_776,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_765,c_125])).

tff(c_899,plain,(
    k7_relat_1('#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_877,c_776])).

tff(c_907,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_906,c_899])).

tff(c_910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_527,c_907])).

tff(c_911,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1003,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_911])).

tff(c_11493,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11476,c_1003])).

tff(c_11521,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_1371,c_1372,c_2251,c_1520,c_2251,c_1520,c_2689,c_11493])).

tff(c_11523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_11521])).

tff(c_11524,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_911])).

tff(c_22235,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22218,c_11524])).

tff(c_22263,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_11900,c_11901,c_13083,c_12082,c_13083,c_12082,c_13976,c_22235])).

tff(c_22265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_22263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.16/6.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.23/6.68  
% 14.23/6.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.23/6.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 14.23/6.68  
% 14.23/6.68  %Foreground sorts:
% 14.23/6.68  
% 14.23/6.68  
% 14.23/6.68  %Background operators:
% 14.23/6.68  
% 14.23/6.68  
% 14.23/6.68  %Foreground operators:
% 14.23/6.68  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 14.23/6.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.23/6.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.23/6.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.23/6.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.23/6.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.23/6.68  tff('#skF_7', type, '#skF_7': $i).
% 14.23/6.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.23/6.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.23/6.68  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.23/6.68  tff('#skF_5', type, '#skF_5': $i).
% 14.23/6.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.23/6.68  tff('#skF_6', type, '#skF_6': $i).
% 14.23/6.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.23/6.68  tff('#skF_2', type, '#skF_2': $i).
% 14.23/6.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.23/6.68  tff('#skF_3', type, '#skF_3': $i).
% 14.23/6.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.23/6.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.23/6.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.23/6.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.23/6.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.23/6.68  tff('#skF_4', type, '#skF_4': $i).
% 14.23/6.68  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.23/6.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.23/6.68  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 14.23/6.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.23/6.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.23/6.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.23/6.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.23/6.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.23/6.68  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 14.23/6.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.23/6.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.23/6.68  
% 14.23/6.71  tff(f_269, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 14.23/6.71  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.23/6.71  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 14.23/6.71  tff(f_65, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 14.23/6.71  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 14.23/6.71  tff(f_107, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 14.23/6.71  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 14.23/6.71  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 14.23/6.71  tff(f_227, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 14.23/6.71  tff(f_145, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 14.23/6.71  tff(f_193, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 14.23/6.71  tff(c_94, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_88, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_84, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_951, plain, (![C_380, A_381, B_382]: (v1_relat_1(C_380) | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.23/6.71  tff(c_964, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_951])).
% 14.23/6.71  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.23/6.71  tff(c_18, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.23/6.71  tff(c_11656, plain, (![A_1611, B_1612, C_1613]: (~r1_xboole_0(A_1611, B_1612) | ~r2_hidden(C_1613, B_1612) | ~r2_hidden(C_1613, A_1611))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.23/6.71  tff(c_11666, plain, (![C_1614]: (~r2_hidden(C_1614, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_11656])).
% 14.23/6.71  tff(c_11676, plain, (![B_4]: (r1_xboole_0(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_10, c_11666])).
% 14.23/6.71  tff(c_11868, plain, (![A_1640, B_1641]: (k7_relat_1(A_1640, B_1641)=k1_xboole_0 | ~r1_xboole_0(B_1641, k1_relat_1(A_1640)) | ~v1_relat_1(A_1640))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.23/6.71  tff(c_11889, plain, (![A_1642]: (k7_relat_1(A_1642, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_1642))), inference(resolution, [status(thm)], [c_11676, c_11868])).
% 14.23/6.71  tff(c_11900, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_964, c_11889])).
% 14.23/6.71  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_963, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_951])).
% 14.23/6.71  tff(c_11901, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_963, c_11889])).
% 14.23/6.71  tff(c_90, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_86, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_82, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_12001, plain, (![A_1658, B_1659]: (r1_xboole_0(A_1658, B_1659) | ~r1_subset_1(A_1658, B_1659) | v1_xboole_0(B_1659) | v1_xboole_0(A_1658))), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.23/6.71  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.23/6.71  tff(c_13077, plain, (![A_1775, B_1776]: (k3_xboole_0(A_1775, B_1776)=k1_xboole_0 | ~r1_subset_1(A_1775, B_1776) | v1_xboole_0(B_1776) | v1_xboole_0(A_1775))), inference(resolution, [status(thm)], [c_12001, c_2])).
% 14.23/6.71  tff(c_13080, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_13077])).
% 14.23/6.71  tff(c_13083, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_13080])).
% 14.23/6.71  tff(c_12067, plain, (![A_1667, B_1668, C_1669]: (k9_subset_1(A_1667, B_1668, C_1669)=k3_xboole_0(B_1668, C_1669) | ~m1_subset_1(C_1669, k1_zfmisc_1(A_1667)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.23/6.71  tff(c_12082, plain, (![B_1668]: (k9_subset_1('#skF_2', B_1668, '#skF_5')=k3_xboole_0(B_1668, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_12067])).
% 14.23/6.71  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_92, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_72, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_13187, plain, (![D_1789, F_1790, A_1792, C_1791, E_1793, B_1794]: (v1_funct_1(k1_tmap_1(A_1792, B_1794, C_1791, D_1789, E_1793, F_1790)) | ~m1_subset_1(F_1790, k1_zfmisc_1(k2_zfmisc_1(D_1789, B_1794))) | ~v1_funct_2(F_1790, D_1789, B_1794) | ~v1_funct_1(F_1790) | ~m1_subset_1(E_1793, k1_zfmisc_1(k2_zfmisc_1(C_1791, B_1794))) | ~v1_funct_2(E_1793, C_1791, B_1794) | ~v1_funct_1(E_1793) | ~m1_subset_1(D_1789, k1_zfmisc_1(A_1792)) | v1_xboole_0(D_1789) | ~m1_subset_1(C_1791, k1_zfmisc_1(A_1792)) | v1_xboole_0(C_1791) | v1_xboole_0(B_1794) | v1_xboole_0(A_1792))), inference(cnfTransformation, [status(thm)], [f_227])).
% 14.23/6.71  tff(c_13192, plain, (![A_1792, C_1791, E_1793]: (v1_funct_1(k1_tmap_1(A_1792, '#skF_3', C_1791, '#skF_5', E_1793, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1793, k1_zfmisc_1(k2_zfmisc_1(C_1791, '#skF_3'))) | ~v1_funct_2(E_1793, C_1791, '#skF_3') | ~v1_funct_1(E_1793) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1792)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1791, k1_zfmisc_1(A_1792)) | v1_xboole_0(C_1791) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1792))), inference(resolution, [status(thm)], [c_70, c_13187])).
% 14.23/6.71  tff(c_13198, plain, (![A_1792, C_1791, E_1793]: (v1_funct_1(k1_tmap_1(A_1792, '#skF_3', C_1791, '#skF_5', E_1793, '#skF_7')) | ~m1_subset_1(E_1793, k1_zfmisc_1(k2_zfmisc_1(C_1791, '#skF_3'))) | ~v1_funct_2(E_1793, C_1791, '#skF_3') | ~v1_funct_1(E_1793) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1792)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1791, k1_zfmisc_1(A_1792)) | v1_xboole_0(C_1791) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1792))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_13192])).
% 14.23/6.71  tff(c_13748, plain, (![A_1869, C_1870, E_1871]: (v1_funct_1(k1_tmap_1(A_1869, '#skF_3', C_1870, '#skF_5', E_1871, '#skF_7')) | ~m1_subset_1(E_1871, k1_zfmisc_1(k2_zfmisc_1(C_1870, '#skF_3'))) | ~v1_funct_2(E_1871, C_1870, '#skF_3') | ~v1_funct_1(E_1871) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1869)) | ~m1_subset_1(C_1870, k1_zfmisc_1(A_1869)) | v1_xboole_0(C_1870) | v1_xboole_0(A_1869))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_13198])).
% 14.23/6.71  tff(c_13758, plain, (![A_1869]: (v1_funct_1(k1_tmap_1(A_1869, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1869)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1869)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1869))), inference(resolution, [status(thm)], [c_76, c_13748])).
% 14.23/6.71  tff(c_13769, plain, (![A_1869]: (v1_funct_1(k1_tmap_1(A_1869, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1869)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1869)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1869))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_13758])).
% 14.23/6.71  tff(c_13964, plain, (![A_1903]: (v1_funct_1(k1_tmap_1(A_1903, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1903)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1903)) | v1_xboole_0(A_1903))), inference(negUnitSimplification, [status(thm)], [c_90, c_13769])).
% 14.23/6.71  tff(c_13971, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_13964])).
% 14.23/6.71  tff(c_13975, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_13971])).
% 14.23/6.71  tff(c_13976, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_13975])).
% 14.23/6.71  tff(c_13029, plain, (![A_1766, B_1767, C_1768, D_1769]: (k2_partfun1(A_1766, B_1767, C_1768, D_1769)=k7_relat_1(C_1768, D_1769) | ~m1_subset_1(C_1768, k1_zfmisc_1(k2_zfmisc_1(A_1766, B_1767))) | ~v1_funct_1(C_1768))), inference(cnfTransformation, [status(thm)], [f_145])).
% 14.23/6.71  tff(c_13036, plain, (![D_1769]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1769)=k7_relat_1('#skF_6', D_1769) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_13029])).
% 14.23/6.71  tff(c_13043, plain, (![D_1769]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1769)=k7_relat_1('#skF_6', D_1769))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_13036])).
% 14.23/6.71  tff(c_13034, plain, (![D_1769]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1769)=k7_relat_1('#skF_7', D_1769) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_13029])).
% 14.23/6.71  tff(c_13040, plain, (![D_1769]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1769)=k7_relat_1('#skF_7', D_1769))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_13034])).
% 14.23/6.71  tff(c_64, plain, (![B_172, A_171, C_173, E_175, F_176, D_174]: (v1_funct_2(k1_tmap_1(A_171, B_172, C_173, D_174, E_175, F_176), k4_subset_1(A_171, C_173, D_174), B_172) | ~m1_subset_1(F_176, k1_zfmisc_1(k2_zfmisc_1(D_174, B_172))) | ~v1_funct_2(F_176, D_174, B_172) | ~v1_funct_1(F_176) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(C_173, B_172))) | ~v1_funct_2(E_175, C_173, B_172) | ~v1_funct_1(E_175) | ~m1_subset_1(D_174, k1_zfmisc_1(A_171)) | v1_xboole_0(D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(A_171)) | v1_xboole_0(C_173) | v1_xboole_0(B_172) | v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_227])).
% 14.23/6.71  tff(c_62, plain, (![B_172, A_171, C_173, E_175, F_176, D_174]: (m1_subset_1(k1_tmap_1(A_171, B_172, C_173, D_174, E_175, F_176), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_171, C_173, D_174), B_172))) | ~m1_subset_1(F_176, k1_zfmisc_1(k2_zfmisc_1(D_174, B_172))) | ~v1_funct_2(F_176, D_174, B_172) | ~v1_funct_1(F_176) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(C_173, B_172))) | ~v1_funct_2(E_175, C_173, B_172) | ~v1_funct_1(E_175) | ~m1_subset_1(D_174, k1_zfmisc_1(A_171)) | v1_xboole_0(D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(A_171)) | v1_xboole_0(C_173) | v1_xboole_0(B_172) | v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_227])).
% 14.23/6.71  tff(c_13536, plain, (![D_1845, C_1844, E_1842, A_1843, F_1840, B_1841]: (k2_partfun1(k4_subset_1(A_1843, C_1844, D_1845), B_1841, k1_tmap_1(A_1843, B_1841, C_1844, D_1845, E_1842, F_1840), C_1844)=E_1842 | ~m1_subset_1(k1_tmap_1(A_1843, B_1841, C_1844, D_1845, E_1842, F_1840), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1843, C_1844, D_1845), B_1841))) | ~v1_funct_2(k1_tmap_1(A_1843, B_1841, C_1844, D_1845, E_1842, F_1840), k4_subset_1(A_1843, C_1844, D_1845), B_1841) | ~v1_funct_1(k1_tmap_1(A_1843, B_1841, C_1844, D_1845, E_1842, F_1840)) | k2_partfun1(D_1845, B_1841, F_1840, k9_subset_1(A_1843, C_1844, D_1845))!=k2_partfun1(C_1844, B_1841, E_1842, k9_subset_1(A_1843, C_1844, D_1845)) | ~m1_subset_1(F_1840, k1_zfmisc_1(k2_zfmisc_1(D_1845, B_1841))) | ~v1_funct_2(F_1840, D_1845, B_1841) | ~v1_funct_1(F_1840) | ~m1_subset_1(E_1842, k1_zfmisc_1(k2_zfmisc_1(C_1844, B_1841))) | ~v1_funct_2(E_1842, C_1844, B_1841) | ~v1_funct_1(E_1842) | ~m1_subset_1(D_1845, k1_zfmisc_1(A_1843)) | v1_xboole_0(D_1845) | ~m1_subset_1(C_1844, k1_zfmisc_1(A_1843)) | v1_xboole_0(C_1844) | v1_xboole_0(B_1841) | v1_xboole_0(A_1843))), inference(cnfTransformation, [status(thm)], [f_193])).
% 14.23/6.71  tff(c_15252, plain, (![F_2063, A_2065, B_2067, E_2066, D_2062, C_2064]: (k2_partfun1(k4_subset_1(A_2065, C_2064, D_2062), B_2067, k1_tmap_1(A_2065, B_2067, C_2064, D_2062, E_2066, F_2063), C_2064)=E_2066 | ~v1_funct_2(k1_tmap_1(A_2065, B_2067, C_2064, D_2062, E_2066, F_2063), k4_subset_1(A_2065, C_2064, D_2062), B_2067) | ~v1_funct_1(k1_tmap_1(A_2065, B_2067, C_2064, D_2062, E_2066, F_2063)) | k2_partfun1(D_2062, B_2067, F_2063, k9_subset_1(A_2065, C_2064, D_2062))!=k2_partfun1(C_2064, B_2067, E_2066, k9_subset_1(A_2065, C_2064, D_2062)) | ~m1_subset_1(F_2063, k1_zfmisc_1(k2_zfmisc_1(D_2062, B_2067))) | ~v1_funct_2(F_2063, D_2062, B_2067) | ~v1_funct_1(F_2063) | ~m1_subset_1(E_2066, k1_zfmisc_1(k2_zfmisc_1(C_2064, B_2067))) | ~v1_funct_2(E_2066, C_2064, B_2067) | ~v1_funct_1(E_2066) | ~m1_subset_1(D_2062, k1_zfmisc_1(A_2065)) | v1_xboole_0(D_2062) | ~m1_subset_1(C_2064, k1_zfmisc_1(A_2065)) | v1_xboole_0(C_2064) | v1_xboole_0(B_2067) | v1_xboole_0(A_2065))), inference(resolution, [status(thm)], [c_62, c_13536])).
% 14.23/6.71  tff(c_21460, plain, (![A_2714, D_2711, B_2716, E_2715, C_2713, F_2712]: (k2_partfun1(k4_subset_1(A_2714, C_2713, D_2711), B_2716, k1_tmap_1(A_2714, B_2716, C_2713, D_2711, E_2715, F_2712), C_2713)=E_2715 | ~v1_funct_1(k1_tmap_1(A_2714, B_2716, C_2713, D_2711, E_2715, F_2712)) | k2_partfun1(D_2711, B_2716, F_2712, k9_subset_1(A_2714, C_2713, D_2711))!=k2_partfun1(C_2713, B_2716, E_2715, k9_subset_1(A_2714, C_2713, D_2711)) | ~m1_subset_1(F_2712, k1_zfmisc_1(k2_zfmisc_1(D_2711, B_2716))) | ~v1_funct_2(F_2712, D_2711, B_2716) | ~v1_funct_1(F_2712) | ~m1_subset_1(E_2715, k1_zfmisc_1(k2_zfmisc_1(C_2713, B_2716))) | ~v1_funct_2(E_2715, C_2713, B_2716) | ~v1_funct_1(E_2715) | ~m1_subset_1(D_2711, k1_zfmisc_1(A_2714)) | v1_xboole_0(D_2711) | ~m1_subset_1(C_2713, k1_zfmisc_1(A_2714)) | v1_xboole_0(C_2713) | v1_xboole_0(B_2716) | v1_xboole_0(A_2714))), inference(resolution, [status(thm)], [c_64, c_15252])).
% 14.23/6.71  tff(c_21467, plain, (![A_2714, C_2713, E_2715]: (k2_partfun1(k4_subset_1(A_2714, C_2713, '#skF_5'), '#skF_3', k1_tmap_1(A_2714, '#skF_3', C_2713, '#skF_5', E_2715, '#skF_7'), C_2713)=E_2715 | ~v1_funct_1(k1_tmap_1(A_2714, '#skF_3', C_2713, '#skF_5', E_2715, '#skF_7')) | k2_partfun1(C_2713, '#skF_3', E_2715, k9_subset_1(A_2714, C_2713, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_2714, C_2713, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2715, k1_zfmisc_1(k2_zfmisc_1(C_2713, '#skF_3'))) | ~v1_funct_2(E_2715, C_2713, '#skF_3') | ~v1_funct_1(E_2715) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2714)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2713, k1_zfmisc_1(A_2714)) | v1_xboole_0(C_2713) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2714))), inference(resolution, [status(thm)], [c_70, c_21460])).
% 14.23/6.71  tff(c_21474, plain, (![A_2714, C_2713, E_2715]: (k2_partfun1(k4_subset_1(A_2714, C_2713, '#skF_5'), '#skF_3', k1_tmap_1(A_2714, '#skF_3', C_2713, '#skF_5', E_2715, '#skF_7'), C_2713)=E_2715 | ~v1_funct_1(k1_tmap_1(A_2714, '#skF_3', C_2713, '#skF_5', E_2715, '#skF_7')) | k2_partfun1(C_2713, '#skF_3', E_2715, k9_subset_1(A_2714, C_2713, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2714, C_2713, '#skF_5')) | ~m1_subset_1(E_2715, k1_zfmisc_1(k2_zfmisc_1(C_2713, '#skF_3'))) | ~v1_funct_2(E_2715, C_2713, '#skF_3') | ~v1_funct_1(E_2715) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2714)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2713, k1_zfmisc_1(A_2714)) | v1_xboole_0(C_2713) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2714))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_13040, c_21467])).
% 14.23/6.71  tff(c_22195, plain, (![A_2770, C_2771, E_2772]: (k2_partfun1(k4_subset_1(A_2770, C_2771, '#skF_5'), '#skF_3', k1_tmap_1(A_2770, '#skF_3', C_2771, '#skF_5', E_2772, '#skF_7'), C_2771)=E_2772 | ~v1_funct_1(k1_tmap_1(A_2770, '#skF_3', C_2771, '#skF_5', E_2772, '#skF_7')) | k2_partfun1(C_2771, '#skF_3', E_2772, k9_subset_1(A_2770, C_2771, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2770, C_2771, '#skF_5')) | ~m1_subset_1(E_2772, k1_zfmisc_1(k2_zfmisc_1(C_2771, '#skF_3'))) | ~v1_funct_2(E_2772, C_2771, '#skF_3') | ~v1_funct_1(E_2772) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2770)) | ~m1_subset_1(C_2771, k1_zfmisc_1(A_2770)) | v1_xboole_0(C_2771) | v1_xboole_0(A_2770))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_21474])).
% 14.23/6.71  tff(c_22205, plain, (![A_2770]: (k2_partfun1(k4_subset_1(A_2770, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2770, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2770, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_2770, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2770, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2770)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2770)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2770))), inference(resolution, [status(thm)], [c_76, c_22195])).
% 14.23/6.71  tff(c_22216, plain, (![A_2770]: (k2_partfun1(k4_subset_1(A_2770, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2770, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2770, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2770, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2770, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2770)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2770)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2770))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_13043, c_22205])).
% 14.23/6.71  tff(c_22218, plain, (![A_2773]: (k2_partfun1(k4_subset_1(A_2773, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2773, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2773, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2773, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2773, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2773)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2773)) | v1_xboole_0(A_2773))), inference(negUnitSimplification, [status(thm)], [c_90, c_22216])).
% 14.23/6.71  tff(c_1063, plain, (![A_407, B_408, C_409]: (~r1_xboole_0(A_407, B_408) | ~r2_hidden(C_409, B_408) | ~r2_hidden(C_409, A_407))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.23/6.71  tff(c_1070, plain, (![C_410]: (~r2_hidden(C_410, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_1063])).
% 14.23/6.71  tff(c_1080, plain, (![B_4]: (r1_xboole_0(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_10, c_1070])).
% 14.23/6.71  tff(c_1334, plain, (![A_450, B_451]: (k7_relat_1(A_450, B_451)=k1_xboole_0 | ~r1_xboole_0(B_451, k1_relat_1(A_450)) | ~v1_relat_1(A_450))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.23/6.71  tff(c_1360, plain, (![A_452]: (k7_relat_1(A_452, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_452))), inference(resolution, [status(thm)], [c_1080, c_1334])).
% 14.23/6.71  tff(c_1371, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_964, c_1360])).
% 14.23/6.71  tff(c_1372, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_963, c_1360])).
% 14.23/6.71  tff(c_1237, plain, (![A_432, B_433]: (r1_xboole_0(A_432, B_433) | ~r1_subset_1(A_432, B_433) | v1_xboole_0(B_433) | v1_xboole_0(A_432))), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.23/6.71  tff(c_2245, plain, (![A_569, B_570]: (k3_xboole_0(A_569, B_570)=k1_xboole_0 | ~r1_subset_1(A_569, B_570) | v1_xboole_0(B_570) | v1_xboole_0(A_569))), inference(resolution, [status(thm)], [c_1237, c_2])).
% 14.23/6.71  tff(c_2248, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_2245])).
% 14.23/6.71  tff(c_2251, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_2248])).
% 14.23/6.71  tff(c_1505, plain, (![A_471, B_472, C_473]: (k9_subset_1(A_471, B_472, C_473)=k3_xboole_0(B_472, C_473) | ~m1_subset_1(C_473, k1_zfmisc_1(A_471)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.23/6.71  tff(c_1520, plain, (![B_472]: (k9_subset_1('#skF_2', B_472, '#skF_5')=k3_xboole_0(B_472, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_1505])).
% 14.23/6.71  tff(c_2371, plain, (![C_584, B_587, E_586, D_582, F_583, A_585]: (v1_funct_1(k1_tmap_1(A_585, B_587, C_584, D_582, E_586, F_583)) | ~m1_subset_1(F_583, k1_zfmisc_1(k2_zfmisc_1(D_582, B_587))) | ~v1_funct_2(F_583, D_582, B_587) | ~v1_funct_1(F_583) | ~m1_subset_1(E_586, k1_zfmisc_1(k2_zfmisc_1(C_584, B_587))) | ~v1_funct_2(E_586, C_584, B_587) | ~v1_funct_1(E_586) | ~m1_subset_1(D_582, k1_zfmisc_1(A_585)) | v1_xboole_0(D_582) | ~m1_subset_1(C_584, k1_zfmisc_1(A_585)) | v1_xboole_0(C_584) | v1_xboole_0(B_587) | v1_xboole_0(A_585))), inference(cnfTransformation, [status(thm)], [f_227])).
% 14.23/6.71  tff(c_2376, plain, (![A_585, C_584, E_586]: (v1_funct_1(k1_tmap_1(A_585, '#skF_3', C_584, '#skF_5', E_586, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_586, k1_zfmisc_1(k2_zfmisc_1(C_584, '#skF_3'))) | ~v1_funct_2(E_586, C_584, '#skF_3') | ~v1_funct_1(E_586) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_585)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_584, k1_zfmisc_1(A_585)) | v1_xboole_0(C_584) | v1_xboole_0('#skF_3') | v1_xboole_0(A_585))), inference(resolution, [status(thm)], [c_70, c_2371])).
% 14.23/6.71  tff(c_2382, plain, (![A_585, C_584, E_586]: (v1_funct_1(k1_tmap_1(A_585, '#skF_3', C_584, '#skF_5', E_586, '#skF_7')) | ~m1_subset_1(E_586, k1_zfmisc_1(k2_zfmisc_1(C_584, '#skF_3'))) | ~v1_funct_2(E_586, C_584, '#skF_3') | ~v1_funct_1(E_586) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_585)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_584, k1_zfmisc_1(A_585)) | v1_xboole_0(C_584) | v1_xboole_0('#skF_3') | v1_xboole_0(A_585))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2376])).
% 14.23/6.71  tff(c_2449, plain, (![A_591, C_592, E_593]: (v1_funct_1(k1_tmap_1(A_591, '#skF_3', C_592, '#skF_5', E_593, '#skF_7')) | ~m1_subset_1(E_593, k1_zfmisc_1(k2_zfmisc_1(C_592, '#skF_3'))) | ~v1_funct_2(E_593, C_592, '#skF_3') | ~v1_funct_1(E_593) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_591)) | ~m1_subset_1(C_592, k1_zfmisc_1(A_591)) | v1_xboole_0(C_592) | v1_xboole_0(A_591))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_2382])).
% 14.23/6.71  tff(c_2456, plain, (![A_591]: (v1_funct_1(k1_tmap_1(A_591, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_591)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_591)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_591))), inference(resolution, [status(thm)], [c_76, c_2449])).
% 14.23/6.71  tff(c_2464, plain, (![A_591]: (v1_funct_1(k1_tmap_1(A_591, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_591)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_591)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_591))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2456])).
% 14.23/6.71  tff(c_2677, plain, (![A_628]: (v1_funct_1(k1_tmap_1(A_628, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_628)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_628)) | v1_xboole_0(A_628))), inference(negUnitSimplification, [status(thm)], [c_90, c_2464])).
% 14.23/6.71  tff(c_2684, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_2677])).
% 14.23/6.71  tff(c_2688, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2684])).
% 14.23/6.71  tff(c_2689, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_2688])).
% 14.23/6.71  tff(c_2119, plain, (![A_551, B_552, C_553, D_554]: (k2_partfun1(A_551, B_552, C_553, D_554)=k7_relat_1(C_553, D_554) | ~m1_subset_1(C_553, k1_zfmisc_1(k2_zfmisc_1(A_551, B_552))) | ~v1_funct_1(C_553))), inference(cnfTransformation, [status(thm)], [f_145])).
% 14.23/6.71  tff(c_2126, plain, (![D_554]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_554)=k7_relat_1('#skF_6', D_554) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_2119])).
% 14.23/6.71  tff(c_2133, plain, (![D_554]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_554)=k7_relat_1('#skF_6', D_554))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2126])).
% 14.23/6.71  tff(c_2124, plain, (![D_554]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_554)=k7_relat_1('#skF_7', D_554) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_2119])).
% 14.23/6.71  tff(c_2130, plain, (![D_554]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_554)=k7_relat_1('#skF_7', D_554))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2124])).
% 14.23/6.71  tff(c_2736, plain, (![F_639, D_644, E_641, B_640, A_642, C_643]: (k2_partfun1(k4_subset_1(A_642, C_643, D_644), B_640, k1_tmap_1(A_642, B_640, C_643, D_644, E_641, F_639), D_644)=F_639 | ~m1_subset_1(k1_tmap_1(A_642, B_640, C_643, D_644, E_641, F_639), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_642, C_643, D_644), B_640))) | ~v1_funct_2(k1_tmap_1(A_642, B_640, C_643, D_644, E_641, F_639), k4_subset_1(A_642, C_643, D_644), B_640) | ~v1_funct_1(k1_tmap_1(A_642, B_640, C_643, D_644, E_641, F_639)) | k2_partfun1(D_644, B_640, F_639, k9_subset_1(A_642, C_643, D_644))!=k2_partfun1(C_643, B_640, E_641, k9_subset_1(A_642, C_643, D_644)) | ~m1_subset_1(F_639, k1_zfmisc_1(k2_zfmisc_1(D_644, B_640))) | ~v1_funct_2(F_639, D_644, B_640) | ~v1_funct_1(F_639) | ~m1_subset_1(E_641, k1_zfmisc_1(k2_zfmisc_1(C_643, B_640))) | ~v1_funct_2(E_641, C_643, B_640) | ~v1_funct_1(E_641) | ~m1_subset_1(D_644, k1_zfmisc_1(A_642)) | v1_xboole_0(D_644) | ~m1_subset_1(C_643, k1_zfmisc_1(A_642)) | v1_xboole_0(C_643) | v1_xboole_0(B_640) | v1_xboole_0(A_642))), inference(cnfTransformation, [status(thm)], [f_193])).
% 14.23/6.71  tff(c_4465, plain, (![D_869, A_872, B_874, E_873, F_870, C_871]: (k2_partfun1(k4_subset_1(A_872, C_871, D_869), B_874, k1_tmap_1(A_872, B_874, C_871, D_869, E_873, F_870), D_869)=F_870 | ~v1_funct_2(k1_tmap_1(A_872, B_874, C_871, D_869, E_873, F_870), k4_subset_1(A_872, C_871, D_869), B_874) | ~v1_funct_1(k1_tmap_1(A_872, B_874, C_871, D_869, E_873, F_870)) | k2_partfun1(D_869, B_874, F_870, k9_subset_1(A_872, C_871, D_869))!=k2_partfun1(C_871, B_874, E_873, k9_subset_1(A_872, C_871, D_869)) | ~m1_subset_1(F_870, k1_zfmisc_1(k2_zfmisc_1(D_869, B_874))) | ~v1_funct_2(F_870, D_869, B_874) | ~v1_funct_1(F_870) | ~m1_subset_1(E_873, k1_zfmisc_1(k2_zfmisc_1(C_871, B_874))) | ~v1_funct_2(E_873, C_871, B_874) | ~v1_funct_1(E_873) | ~m1_subset_1(D_869, k1_zfmisc_1(A_872)) | v1_xboole_0(D_869) | ~m1_subset_1(C_871, k1_zfmisc_1(A_872)) | v1_xboole_0(C_871) | v1_xboole_0(B_874) | v1_xboole_0(A_872))), inference(resolution, [status(thm)], [c_62, c_2736])).
% 14.23/6.71  tff(c_10552, plain, (![A_1505, D_1502, E_1506, C_1504, F_1503, B_1507]: (k2_partfun1(k4_subset_1(A_1505, C_1504, D_1502), B_1507, k1_tmap_1(A_1505, B_1507, C_1504, D_1502, E_1506, F_1503), D_1502)=F_1503 | ~v1_funct_1(k1_tmap_1(A_1505, B_1507, C_1504, D_1502, E_1506, F_1503)) | k2_partfun1(D_1502, B_1507, F_1503, k9_subset_1(A_1505, C_1504, D_1502))!=k2_partfun1(C_1504, B_1507, E_1506, k9_subset_1(A_1505, C_1504, D_1502)) | ~m1_subset_1(F_1503, k1_zfmisc_1(k2_zfmisc_1(D_1502, B_1507))) | ~v1_funct_2(F_1503, D_1502, B_1507) | ~v1_funct_1(F_1503) | ~m1_subset_1(E_1506, k1_zfmisc_1(k2_zfmisc_1(C_1504, B_1507))) | ~v1_funct_2(E_1506, C_1504, B_1507) | ~v1_funct_1(E_1506) | ~m1_subset_1(D_1502, k1_zfmisc_1(A_1505)) | v1_xboole_0(D_1502) | ~m1_subset_1(C_1504, k1_zfmisc_1(A_1505)) | v1_xboole_0(C_1504) | v1_xboole_0(B_1507) | v1_xboole_0(A_1505))), inference(resolution, [status(thm)], [c_64, c_4465])).
% 14.23/6.71  tff(c_10559, plain, (![A_1505, C_1504, E_1506]: (k2_partfun1(k4_subset_1(A_1505, C_1504, '#skF_5'), '#skF_3', k1_tmap_1(A_1505, '#skF_3', C_1504, '#skF_5', E_1506, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1505, '#skF_3', C_1504, '#skF_5', E_1506, '#skF_7')) | k2_partfun1(C_1504, '#skF_3', E_1506, k9_subset_1(A_1505, C_1504, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1505, C_1504, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1506, k1_zfmisc_1(k2_zfmisc_1(C_1504, '#skF_3'))) | ~v1_funct_2(E_1506, C_1504, '#skF_3') | ~v1_funct_1(E_1506) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1505)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1504, k1_zfmisc_1(A_1505)) | v1_xboole_0(C_1504) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1505))), inference(resolution, [status(thm)], [c_70, c_10552])).
% 14.23/6.71  tff(c_10566, plain, (![A_1505, C_1504, E_1506]: (k2_partfun1(k4_subset_1(A_1505, C_1504, '#skF_5'), '#skF_3', k1_tmap_1(A_1505, '#skF_3', C_1504, '#skF_5', E_1506, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1505, '#skF_3', C_1504, '#skF_5', E_1506, '#skF_7')) | k2_partfun1(C_1504, '#skF_3', E_1506, k9_subset_1(A_1505, C_1504, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1505, C_1504, '#skF_5')) | ~m1_subset_1(E_1506, k1_zfmisc_1(k2_zfmisc_1(C_1504, '#skF_3'))) | ~v1_funct_2(E_1506, C_1504, '#skF_3') | ~v1_funct_1(E_1506) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1505)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1504, k1_zfmisc_1(A_1505)) | v1_xboole_0(C_1504) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1505))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2130, c_10559])).
% 14.23/6.71  tff(c_11453, plain, (![A_1578, C_1579, E_1580]: (k2_partfun1(k4_subset_1(A_1578, C_1579, '#skF_5'), '#skF_3', k1_tmap_1(A_1578, '#skF_3', C_1579, '#skF_5', E_1580, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1578, '#skF_3', C_1579, '#skF_5', E_1580, '#skF_7')) | k2_partfun1(C_1579, '#skF_3', E_1580, k9_subset_1(A_1578, C_1579, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1578, C_1579, '#skF_5')) | ~m1_subset_1(E_1580, k1_zfmisc_1(k2_zfmisc_1(C_1579, '#skF_3'))) | ~v1_funct_2(E_1580, C_1579, '#skF_3') | ~v1_funct_1(E_1580) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1578)) | ~m1_subset_1(C_1579, k1_zfmisc_1(A_1578)) | v1_xboole_0(C_1579) | v1_xboole_0(A_1578))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_10566])).
% 14.23/6.71  tff(c_11463, plain, (![A_1578]: (k2_partfun1(k4_subset_1(A_1578, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1578, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1578, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1578, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1578, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1578)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1578)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1578))), inference(resolution, [status(thm)], [c_76, c_11453])).
% 14.23/6.71  tff(c_11474, plain, (![A_1578]: (k2_partfun1(k4_subset_1(A_1578, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1578, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1578, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1578, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1578, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1578)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1578)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1578))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2133, c_11463])).
% 14.23/6.71  tff(c_11476, plain, (![A_1581]: (k2_partfun1(k4_subset_1(A_1581, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1581, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1581, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1581, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1581, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1581)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1581)) | v1_xboole_0(A_1581))), inference(negUnitSimplification, [status(thm)], [c_90, c_11474])).
% 14.23/6.71  tff(c_183, plain, (![C_253, A_254, B_255]: (v1_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.23/6.71  tff(c_195, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_183])).
% 14.23/6.71  tff(c_404, plain, (![A_296, B_297, C_298]: (~r1_xboole_0(A_296, B_297) | ~r2_hidden(C_298, B_297) | ~r2_hidden(C_298, A_296))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.23/6.71  tff(c_417, plain, (![C_299]: (~r2_hidden(C_299, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_404])).
% 14.23/6.71  tff(c_427, plain, (![B_4]: (r1_xboole_0(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_10, c_417])).
% 14.23/6.71  tff(c_495, plain, (![A_304, B_305]: (k7_relat_1(A_304, B_305)=k1_xboole_0 | ~r1_xboole_0(B_305, k1_relat_1(A_304)) | ~v1_relat_1(A_304))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.23/6.71  tff(c_516, plain, (![A_306]: (k7_relat_1(A_306, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_306))), inference(resolution, [status(thm)], [c_427, c_495])).
% 14.23/6.71  tff(c_528, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_195, c_516])).
% 14.23/6.71  tff(c_196, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_183])).
% 14.23/6.71  tff(c_527, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_196, c_516])).
% 14.23/6.71  tff(c_574, plain, (![A_320, B_321]: (r1_xboole_0(A_320, B_321) | ~r1_subset_1(A_320, B_321) | v1_xboole_0(B_321) | v1_xboole_0(A_320))), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.23/6.71  tff(c_900, plain, (![A_371, B_372]: (k3_xboole_0(A_371, B_372)=k1_xboole_0 | ~r1_subset_1(A_371, B_372) | v1_xboole_0(B_372) | v1_xboole_0(A_371))), inference(resolution, [status(thm)], [c_574, c_2])).
% 14.23/6.71  tff(c_903, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_900])).
% 14.23/6.71  tff(c_906, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_903])).
% 14.23/6.71  tff(c_866, plain, (![A_365, B_366, C_367, D_368]: (k2_partfun1(A_365, B_366, C_367, D_368)=k7_relat_1(C_367, D_368) | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(A_365, B_366))) | ~v1_funct_1(C_367))), inference(cnfTransformation, [status(thm)], [f_145])).
% 14.23/6.71  tff(c_873, plain, (![D_368]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_368)=k7_relat_1('#skF_6', D_368) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_866])).
% 14.23/6.71  tff(c_880, plain, (![D_368]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_368)=k7_relat_1('#skF_6', D_368))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_873])).
% 14.23/6.71  tff(c_871, plain, (![D_368]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_368)=k7_relat_1('#skF_7', D_368) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_866])).
% 14.23/6.71  tff(c_877, plain, (![D_368]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_368)=k7_relat_1('#skF_7', D_368))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_871])).
% 14.23/6.71  tff(c_750, plain, (![A_345, B_346, C_347]: (k9_subset_1(A_345, B_346, C_347)=k3_xboole_0(B_346, C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(A_345)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.23/6.71  tff(c_765, plain, (![B_346]: (k9_subset_1('#skF_2', B_346, '#skF_5')=k3_xboole_0(B_346, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_750])).
% 14.23/6.71  tff(c_68, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_269])).
% 14.23/6.71  tff(c_125, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_68])).
% 14.23/6.71  tff(c_776, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_765, c_765, c_125])).
% 14.23/6.71  tff(c_899, plain, (k7_relat_1('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_880, c_877, c_776])).
% 14.23/6.71  tff(c_907, plain, (k7_relat_1('#skF_7', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_906, c_906, c_899])).
% 14.23/6.71  tff(c_910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_528, c_527, c_907])).
% 14.23/6.71  tff(c_911, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_68])).
% 14.23/6.71  tff(c_1003, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_911])).
% 14.23/6.71  tff(c_11493, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11476, c_1003])).
% 14.23/6.71  tff(c_11521, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_1371, c_1372, c_2251, c_1520, c_2251, c_1520, c_2689, c_11493])).
% 14.23/6.71  tff(c_11523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_11521])).
% 14.23/6.71  tff(c_11524, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_911])).
% 14.23/6.71  tff(c_22235, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22218, c_11524])).
% 14.23/6.71  tff(c_22263, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_11900, c_11901, c_13083, c_12082, c_13083, c_12082, c_13976, c_22235])).
% 14.23/6.71  tff(c_22265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_22263])).
% 14.23/6.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.23/6.71  
% 14.23/6.71  Inference rules
% 14.23/6.71  ----------------------
% 14.23/6.71  #Ref     : 0
% 14.23/6.71  #Sup     : 3937
% 14.23/6.71  #Fact    : 0
% 14.23/6.71  #Define  : 0
% 14.23/6.71  #Split   : 70
% 14.23/6.71  #Chain   : 0
% 14.23/6.71  #Close   : 0
% 14.23/6.71  
% 14.23/6.71  Ordering : KBO
% 14.23/6.71  
% 14.23/6.71  Simplification rules
% 14.23/6.71  ----------------------
% 14.23/6.71  #Subsume      : 850
% 14.23/6.71  #Demod        : 5712
% 14.23/6.71  #Tautology    : 1832
% 14.23/6.71  #SimpNegUnit  : 1707
% 14.23/6.71  #BackRed      : 401
% 14.23/6.71  
% 14.23/6.71  #Partial instantiations: 0
% 14.23/6.71  #Strategies tried      : 1
% 14.23/6.71  
% 14.23/6.71  Timing (in seconds)
% 14.23/6.71  ----------------------
% 14.23/6.72  Preprocessing        : 0.42
% 14.23/6.72  Parsing              : 0.21
% 14.23/6.72  CNF conversion       : 0.06
% 14.23/6.72  Main loop            : 5.48
% 14.23/6.72  Inferencing          : 1.77
% 14.23/6.72  Reduction            : 1.97
% 14.23/6.72  Demodulation         : 1.47
% 14.23/6.72  BG Simplification    : 0.10
% 14.23/6.72  Subsumption          : 1.36
% 14.23/6.72  Abstraction          : 0.16
% 14.23/6.72  MUC search           : 0.00
% 14.23/6.72  Cooper               : 0.00
% 14.23/6.72  Total                : 5.96
% 14.23/6.72  Index Insertion      : 0.00
% 14.23/6.72  Index Deletion       : 0.00
% 14.23/6.72  Index Matching       : 0.00
% 14.23/6.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
