%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:51 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 492 expanded)
%              Number of leaves         :   40 ( 186 expanded)
%              Depth                    :   14
%              Number of atoms          :  281 (1735 expanded)
%              Number of equality atoms :   56 ( 319 expanded)
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

tff(f_139,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
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

tff(f_114,axiom,(
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

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_177,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_190,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_177])).

tff(c_34,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_195,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_34])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2390,plain,(
    ! [C_454,F_453,B_455,A_452,D_457,E_456] :
      ( k1_funct_1(k8_funct_2(B_455,C_454,A_452,D_457,E_456),F_453) = k1_funct_1(E_456,k1_funct_1(D_457,F_453))
      | k1_xboole_0 = B_455
      | ~ r1_tarski(k2_relset_1(B_455,C_454,D_457),k1_relset_1(C_454,A_452,E_456))
      | ~ m1_subset_1(F_453,B_455)
      | ~ m1_subset_1(E_456,k1_zfmisc_1(k2_zfmisc_1(C_454,A_452)))
      | ~ v1_funct_1(E_456)
      | ~ m1_subset_1(D_457,k1_zfmisc_1(k2_zfmisc_1(B_455,C_454)))
      | ~ v1_funct_2(D_457,B_455,C_454)
      | ~ v1_funct_1(D_457)
      | v1_xboole_0(C_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2392,plain,(
    ! [B_455,D_457,F_453] :
      ( k1_funct_1(k8_funct_2(B_455,'#skF_3','#skF_1',D_457,'#skF_5'),F_453) = k1_funct_1('#skF_5',k1_funct_1(D_457,F_453))
      | k1_xboole_0 = B_455
      | ~ r1_tarski(k2_relset_1(B_455,'#skF_3',D_457),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_453,B_455)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_457,k1_zfmisc_1(k2_zfmisc_1(B_455,'#skF_3')))
      | ~ v1_funct_2(D_457,B_455,'#skF_3')
      | ~ v1_funct_1(D_457)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_2390])).

tff(c_2396,plain,(
    ! [B_455,D_457,F_453] :
      ( k1_funct_1(k8_funct_2(B_455,'#skF_3','#skF_1',D_457,'#skF_5'),F_453) = k1_funct_1('#skF_5',k1_funct_1(D_457,F_453))
      | k1_xboole_0 = B_455
      | ~ r1_tarski(k2_relset_1(B_455,'#skF_3',D_457),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_453,B_455)
      | ~ m1_subset_1(D_457,k1_zfmisc_1(k2_zfmisc_1(B_455,'#skF_3')))
      | ~ v1_funct_2(D_457,B_455,'#skF_3')
      | ~ v1_funct_1(D_457)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2392])).

tff(c_2710,plain,(
    ! [B_495,D_496,F_497] :
      ( k1_funct_1(k8_funct_2(B_495,'#skF_3','#skF_1',D_496,'#skF_5'),F_497) = k1_funct_1('#skF_5',k1_funct_1(D_496,F_497))
      | k1_xboole_0 = B_495
      | ~ r1_tarski(k2_relset_1(B_495,'#skF_3',D_496),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_497,B_495)
      | ~ m1_subset_1(D_496,k1_zfmisc_1(k2_zfmisc_1(B_495,'#skF_3')))
      | ~ v1_funct_2(D_496,B_495,'#skF_3')
      | ~ v1_funct_1(D_496) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2396])).

tff(c_2712,plain,(
    ! [F_497] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_497) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_497))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_497,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_195,c_2710])).

tff(c_2715,plain,(
    ! [F_497] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_497) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_497))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_497,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_2712])).

tff(c_2716,plain,(
    ! [F_497] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_497) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_497))
      | ~ m1_subset_1(F_497,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2715])).

tff(c_70,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_107,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_119,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_107])).

tff(c_221,plain,(
    ! [A_105,B_106,C_107] :
      ( k7_partfun1(A_105,B_106,C_107) = k1_funct_1(B_106,C_107)
      | ~ r2_hidden(C_107,k1_relat_1(B_106))
      | ~ v1_funct_1(B_106)
      | ~ v5_relat_1(B_106,A_105)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2730,plain,(
    ! [A_500,B_501,A_502] :
      ( k7_partfun1(A_500,B_501,A_502) = k1_funct_1(B_501,A_502)
      | ~ v1_funct_1(B_501)
      | ~ v5_relat_1(B_501,A_500)
      | ~ v1_relat_1(B_501)
      | v1_xboole_0(k1_relat_1(B_501))
      | ~ m1_subset_1(A_502,k1_relat_1(B_501)) ) ),
    inference(resolution,[status(thm)],[c_6,c_221])).

tff(c_2734,plain,(
    ! [A_502] :
      ( k7_partfun1('#skF_3','#skF_4',A_502) = k1_funct_1('#skF_4',A_502)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_502,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_119,c_2730])).

tff(c_2741,plain,(
    ! [A_502] :
      ( k7_partfun1('#skF_3','#skF_4',A_502) = k1_funct_1('#skF_4',A_502)
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_502,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_46,c_2734])).

tff(c_2743,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2741])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2747,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2743,c_4])).

tff(c_189,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_177])).

tff(c_2394,plain,(
    ! [B_455,D_457,F_453] :
      ( k1_funct_1(k8_funct_2(B_455,'#skF_2','#skF_3',D_457,'#skF_4'),F_453) = k1_funct_1('#skF_4',k1_funct_1(D_457,F_453))
      | k1_xboole_0 = B_455
      | ~ r1_tarski(k2_relset_1(B_455,'#skF_2',D_457),k1_relat_1('#skF_4'))
      | ~ m1_subset_1(F_453,B_455)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(D_457,k1_zfmisc_1(k2_zfmisc_1(B_455,'#skF_2')))
      | ~ v1_funct_2(D_457,B_455,'#skF_2')
      | ~ v1_funct_1(D_457)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_2390])).

tff(c_2399,plain,(
    ! [B_455,D_457,F_453] :
      ( k1_funct_1(k8_funct_2(B_455,'#skF_2','#skF_3',D_457,'#skF_4'),F_453) = k1_funct_1('#skF_4',k1_funct_1(D_457,F_453))
      | k1_xboole_0 = B_455
      | ~ r1_tarski(k2_relset_1(B_455,'#skF_2',D_457),k1_relat_1('#skF_4'))
      | ~ m1_subset_1(F_453,B_455)
      | ~ m1_subset_1(D_457,k1_zfmisc_1(k2_zfmisc_1(B_455,'#skF_2')))
      | ~ v1_funct_2(D_457,B_455,'#skF_2')
      | ~ v1_funct_1(D_457)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_2394])).

tff(c_2809,plain,(
    ! [B_455,D_457,F_453] :
      ( k1_funct_1(k8_funct_2(B_455,'#skF_2','#skF_3',D_457,'#skF_4'),F_453) = k1_funct_1('#skF_4',k1_funct_1(D_457,F_453))
      | k1_xboole_0 = B_455
      | ~ r1_tarski(k2_relset_1(B_455,'#skF_2',D_457),k1_xboole_0)
      | ~ m1_subset_1(F_453,B_455)
      | ~ m1_subset_1(D_457,k1_zfmisc_1(k2_zfmisc_1(B_455,'#skF_2')))
      | ~ v1_funct_2(D_457,B_455,'#skF_2')
      | ~ v1_funct_1(D_457)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2747,c_2399])).

tff(c_2810,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2809])).

tff(c_2813,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2810,c_4])).

tff(c_2817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2813])).

tff(c_2819,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2809])).

tff(c_1664,plain,(
    ! [D_327,C_328,A_329,B_330] :
      ( r2_hidden(k1_funct_1(D_327,C_328),k2_relset_1(A_329,B_330,D_327))
      | k1_xboole_0 = B_330
      | ~ r2_hidden(C_328,A_329)
      | ~ m1_subset_1(D_327,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_2(D_327,A_329,B_330)
      | ~ v1_funct_1(D_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_161,plain,(
    ! [A_88,C_89,B_90] :
      ( m1_subset_1(A_88,C_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(C_89))
      | ~ r2_hidden(A_88,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_168,plain,(
    ! [A_88,B_5,A_4] :
      ( m1_subset_1(A_88,B_5)
      | ~ r2_hidden(A_88,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_161])).

tff(c_2780,plain,(
    ! [D_511,C_513,B_515,B_514,A_512] :
      ( m1_subset_1(k1_funct_1(D_511,C_513),B_514)
      | ~ r1_tarski(k2_relset_1(A_512,B_515,D_511),B_514)
      | k1_xboole_0 = B_515
      | ~ r2_hidden(C_513,A_512)
      | ~ m1_subset_1(D_511,k1_zfmisc_1(k2_zfmisc_1(A_512,B_515)))
      | ~ v1_funct_2(D_511,A_512,B_515)
      | ~ v1_funct_1(D_511) ) ),
    inference(resolution,[status(thm)],[c_1664,c_168])).

tff(c_2782,plain,(
    ! [C_513] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_513),k1_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_513,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_195,c_2780])).

tff(c_2785,plain,(
    ! [C_513] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_513),k1_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_513,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_2782])).

tff(c_2786,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2785])).

tff(c_2798,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2786,c_2])).

tff(c_2801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2798])).

tff(c_2804,plain,(
    ! [C_516] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_516),k1_relat_1('#skF_5'))
      | ~ r2_hidden(C_516,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_2785])).

tff(c_95,plain,(
    ! [C_70,B_71,A_72] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_132,plain,(
    ! [B_79,A_80,A_81] :
      ( ~ v1_xboole_0(B_79)
      | ~ r2_hidden(A_80,A_81)
      | ~ r1_tarski(A_81,B_79) ) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_200,plain,(
    ! [B_99,B_100,A_101] :
      ( ~ v1_xboole_0(B_99)
      | ~ r1_tarski(B_100,B_99)
      | v1_xboole_0(B_100)
      | ~ m1_subset_1(A_101,B_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_207,plain,(
    ! [A_101] :
      ( ~ v1_xboole_0(k1_relat_1('#skF_5'))
      | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(A_101,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_195,c_200])).

tff(c_2400,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_120,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_107])).

tff(c_2732,plain,(
    ! [A_502] :
      ( k7_partfun1('#skF_1','#skF_5',A_502) = k1_funct_1('#skF_5',A_502)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_502,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_120,c_2730])).

tff(c_2737,plain,(
    ! [A_502] :
      ( k7_partfun1('#skF_1','#skF_5',A_502) = k1_funct_1('#skF_5',A_502)
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_502,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_40,c_2732])).

tff(c_2738,plain,(
    ! [A_502] :
      ( k7_partfun1('#skF_1','#skF_5',A_502) = k1_funct_1('#skF_5',A_502)
      | ~ m1_subset_1(A_502,k1_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2400,c_2737])).

tff(c_2820,plain,(
    ! [C_517] :
      ( k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4',C_517)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_517))
      | ~ r2_hidden(C_517,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2804,c_2738])).

tff(c_30,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2826,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2820,c_30])).

tff(c_2832,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2826])).

tff(c_2835,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2832])).

tff(c_2838,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2835])).

tff(c_2840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2819,c_2838])).

tff(c_2841,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2826])).

tff(c_2858,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2716,c_2841])).

tff(c_2862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2858])).

tff(c_2864,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_2868,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2864,c_4])).

tff(c_2870,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2868,c_195])).

tff(c_102,plain,(
    ! [B_5,A_72,A_4] :
      ( ~ v1_xboole_0(B_5)
      | ~ r2_hidden(A_72,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_2958,plain,(
    ! [B_537,C_536,A_535,D_534,B_538] :
      ( ~ v1_xboole_0(B_537)
      | ~ r1_tarski(k2_relset_1(A_535,B_538,D_534),B_537)
      | k1_xboole_0 = B_538
      | ~ r2_hidden(C_536,A_535)
      | ~ m1_subset_1(D_534,k1_zfmisc_1(k2_zfmisc_1(A_535,B_538)))
      | ~ v1_funct_2(D_534,A_535,B_538)
      | ~ v1_funct_1(D_534) ) ),
    inference(resolution,[status(thm)],[c_1664,c_102])).

tff(c_2960,plain,(
    ! [C_536] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_536,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2870,c_2958])).

tff(c_2963,plain,(
    ! [C_536] :
      ( k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_536,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_2,c_2960])).

tff(c_2965,plain,(
    ! [C_539] : ~ r2_hidden(C_539,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2963])).

tff(c_2970,plain,(
    ! [A_2] :
      ( v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_2965])).

tff(c_2971,plain,(
    ! [A_2] : ~ m1_subset_1(A_2,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2970])).

tff(c_2985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2971,c_36])).

tff(c_2986,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2970])).

tff(c_2989,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2986,c_4])).

tff(c_2993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2989])).

tff(c_2994,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2963])).

tff(c_3007,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_2])).

tff(c_3010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 11:42:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.08  
% 5.74/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.09  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.74/2.09  
% 5.74/2.09  %Foreground sorts:
% 5.74/2.09  
% 5.74/2.09  
% 5.74/2.09  %Background operators:
% 5.74/2.09  
% 5.74/2.09  
% 5.74/2.09  %Foreground operators:
% 5.74/2.09  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.74/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.74/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.74/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.74/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.74/2.09  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 5.74/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.74/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.74/2.09  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 5.74/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.74/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.74/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.74/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.74/2.09  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.74/2.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.74/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.74/2.09  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.74/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.74/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.74/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.74/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.74/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.74/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.74/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.74/2.09  
% 5.74/2.11  tff(f_139, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 5.74/2.11  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.74/2.11  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.74/2.11  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.74/2.11  tff(f_102, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 5.74/2.11  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.74/2.11  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.74/2.11  tff(f_78, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 5.74/2.11  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.74/2.11  tff(f_114, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 5.74/2.11  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.74/2.11  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.74/2.11  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.74/2.11  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.74/2.11  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.74/2.11  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.74/2.11  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.74/2.11  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.74/2.11  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.74/2.11  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.74/2.11  tff(c_36, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.74/2.11  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.74/2.11  tff(c_177, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.74/2.11  tff(c_190, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_177])).
% 5.74/2.11  tff(c_34, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.74/2.11  tff(c_195, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_34])).
% 5.74/2.11  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.74/2.11  tff(c_2390, plain, (![C_454, F_453, B_455, A_452, D_457, E_456]: (k1_funct_1(k8_funct_2(B_455, C_454, A_452, D_457, E_456), F_453)=k1_funct_1(E_456, k1_funct_1(D_457, F_453)) | k1_xboole_0=B_455 | ~r1_tarski(k2_relset_1(B_455, C_454, D_457), k1_relset_1(C_454, A_452, E_456)) | ~m1_subset_1(F_453, B_455) | ~m1_subset_1(E_456, k1_zfmisc_1(k2_zfmisc_1(C_454, A_452))) | ~v1_funct_1(E_456) | ~m1_subset_1(D_457, k1_zfmisc_1(k2_zfmisc_1(B_455, C_454))) | ~v1_funct_2(D_457, B_455, C_454) | ~v1_funct_1(D_457) | v1_xboole_0(C_454))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.74/2.11  tff(c_2392, plain, (![B_455, D_457, F_453]: (k1_funct_1(k8_funct_2(B_455, '#skF_3', '#skF_1', D_457, '#skF_5'), F_453)=k1_funct_1('#skF_5', k1_funct_1(D_457, F_453)) | k1_xboole_0=B_455 | ~r1_tarski(k2_relset_1(B_455, '#skF_3', D_457), k1_relat_1('#skF_5')) | ~m1_subset_1(F_453, B_455) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_457, k1_zfmisc_1(k2_zfmisc_1(B_455, '#skF_3'))) | ~v1_funct_2(D_457, B_455, '#skF_3') | ~v1_funct_1(D_457) | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_2390])).
% 5.74/2.11  tff(c_2396, plain, (![B_455, D_457, F_453]: (k1_funct_1(k8_funct_2(B_455, '#skF_3', '#skF_1', D_457, '#skF_5'), F_453)=k1_funct_1('#skF_5', k1_funct_1(D_457, F_453)) | k1_xboole_0=B_455 | ~r1_tarski(k2_relset_1(B_455, '#skF_3', D_457), k1_relat_1('#skF_5')) | ~m1_subset_1(F_453, B_455) | ~m1_subset_1(D_457, k1_zfmisc_1(k2_zfmisc_1(B_455, '#skF_3'))) | ~v1_funct_2(D_457, B_455, '#skF_3') | ~v1_funct_1(D_457) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2392])).
% 5.74/2.11  tff(c_2710, plain, (![B_495, D_496, F_497]: (k1_funct_1(k8_funct_2(B_495, '#skF_3', '#skF_1', D_496, '#skF_5'), F_497)=k1_funct_1('#skF_5', k1_funct_1(D_496, F_497)) | k1_xboole_0=B_495 | ~r1_tarski(k2_relset_1(B_495, '#skF_3', D_496), k1_relat_1('#skF_5')) | ~m1_subset_1(F_497, B_495) | ~m1_subset_1(D_496, k1_zfmisc_1(k2_zfmisc_1(B_495, '#skF_3'))) | ~v1_funct_2(D_496, B_495, '#skF_3') | ~v1_funct_1(D_496))), inference(negUnitSimplification, [status(thm)], [c_48, c_2396])).
% 5.74/2.11  tff(c_2712, plain, (![F_497]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_497)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_497)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_497, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_195, c_2710])).
% 5.74/2.11  tff(c_2715, plain, (![F_497]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_497)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_497)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_497, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_2712])).
% 5.74/2.11  tff(c_2716, plain, (![F_497]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_497)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_497)) | ~m1_subset_1(F_497, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_2715])).
% 5.74/2.11  tff(c_70, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.11  tff(c_82, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_70])).
% 5.74/2.11  tff(c_107, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.74/2.11  tff(c_119, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_107])).
% 5.74/2.11  tff(c_221, plain, (![A_105, B_106, C_107]: (k7_partfun1(A_105, B_106, C_107)=k1_funct_1(B_106, C_107) | ~r2_hidden(C_107, k1_relat_1(B_106)) | ~v1_funct_1(B_106) | ~v5_relat_1(B_106, A_105) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.74/2.11  tff(c_2730, plain, (![A_500, B_501, A_502]: (k7_partfun1(A_500, B_501, A_502)=k1_funct_1(B_501, A_502) | ~v1_funct_1(B_501) | ~v5_relat_1(B_501, A_500) | ~v1_relat_1(B_501) | v1_xboole_0(k1_relat_1(B_501)) | ~m1_subset_1(A_502, k1_relat_1(B_501)))), inference(resolution, [status(thm)], [c_6, c_221])).
% 5.74/2.11  tff(c_2734, plain, (![A_502]: (k7_partfun1('#skF_3', '#skF_4', A_502)=k1_funct_1('#skF_4', A_502) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_502, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_119, c_2730])).
% 5.74/2.11  tff(c_2741, plain, (![A_502]: (k7_partfun1('#skF_3', '#skF_4', A_502)=k1_funct_1('#skF_4', A_502) | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_502, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_46, c_2734])).
% 5.74/2.11  tff(c_2743, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2741])).
% 5.74/2.11  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.74/2.11  tff(c_2747, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2743, c_4])).
% 5.74/2.11  tff(c_189, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_177])).
% 5.74/2.11  tff(c_2394, plain, (![B_455, D_457, F_453]: (k1_funct_1(k8_funct_2(B_455, '#skF_2', '#skF_3', D_457, '#skF_4'), F_453)=k1_funct_1('#skF_4', k1_funct_1(D_457, F_453)) | k1_xboole_0=B_455 | ~r1_tarski(k2_relset_1(B_455, '#skF_2', D_457), k1_relat_1('#skF_4')) | ~m1_subset_1(F_453, B_455) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1(D_457, k1_zfmisc_1(k2_zfmisc_1(B_455, '#skF_2'))) | ~v1_funct_2(D_457, B_455, '#skF_2') | ~v1_funct_1(D_457) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_2390])).
% 5.74/2.11  tff(c_2399, plain, (![B_455, D_457, F_453]: (k1_funct_1(k8_funct_2(B_455, '#skF_2', '#skF_3', D_457, '#skF_4'), F_453)=k1_funct_1('#skF_4', k1_funct_1(D_457, F_453)) | k1_xboole_0=B_455 | ~r1_tarski(k2_relset_1(B_455, '#skF_2', D_457), k1_relat_1('#skF_4')) | ~m1_subset_1(F_453, B_455) | ~m1_subset_1(D_457, k1_zfmisc_1(k2_zfmisc_1(B_455, '#skF_2'))) | ~v1_funct_2(D_457, B_455, '#skF_2') | ~v1_funct_1(D_457) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_2394])).
% 5.74/2.11  tff(c_2809, plain, (![B_455, D_457, F_453]: (k1_funct_1(k8_funct_2(B_455, '#skF_2', '#skF_3', D_457, '#skF_4'), F_453)=k1_funct_1('#skF_4', k1_funct_1(D_457, F_453)) | k1_xboole_0=B_455 | ~r1_tarski(k2_relset_1(B_455, '#skF_2', D_457), k1_xboole_0) | ~m1_subset_1(F_453, B_455) | ~m1_subset_1(D_457, k1_zfmisc_1(k2_zfmisc_1(B_455, '#skF_2'))) | ~v1_funct_2(D_457, B_455, '#skF_2') | ~v1_funct_1(D_457) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2747, c_2399])).
% 5.74/2.11  tff(c_2810, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2809])).
% 5.74/2.11  tff(c_2813, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2810, c_4])).
% 5.74/2.11  tff(c_2817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_2813])).
% 5.74/2.11  tff(c_2819, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_2809])).
% 5.74/2.11  tff(c_1664, plain, (![D_327, C_328, A_329, B_330]: (r2_hidden(k1_funct_1(D_327, C_328), k2_relset_1(A_329, B_330, D_327)) | k1_xboole_0=B_330 | ~r2_hidden(C_328, A_329) | ~m1_subset_1(D_327, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_2(D_327, A_329, B_330) | ~v1_funct_1(D_327))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.74/2.11  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.74/2.11  tff(c_161, plain, (![A_88, C_89, B_90]: (m1_subset_1(A_88, C_89) | ~m1_subset_1(B_90, k1_zfmisc_1(C_89)) | ~r2_hidden(A_88, B_90))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.74/2.11  tff(c_168, plain, (![A_88, B_5, A_4]: (m1_subset_1(A_88, B_5) | ~r2_hidden(A_88, A_4) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_10, c_161])).
% 5.74/2.11  tff(c_2780, plain, (![D_511, C_513, B_515, B_514, A_512]: (m1_subset_1(k1_funct_1(D_511, C_513), B_514) | ~r1_tarski(k2_relset_1(A_512, B_515, D_511), B_514) | k1_xboole_0=B_515 | ~r2_hidden(C_513, A_512) | ~m1_subset_1(D_511, k1_zfmisc_1(k2_zfmisc_1(A_512, B_515))) | ~v1_funct_2(D_511, A_512, B_515) | ~v1_funct_1(D_511))), inference(resolution, [status(thm)], [c_1664, c_168])).
% 5.74/2.11  tff(c_2782, plain, (![C_513]: (m1_subset_1(k1_funct_1('#skF_4', C_513), k1_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_513, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_195, c_2780])).
% 5.74/2.11  tff(c_2785, plain, (![C_513]: (m1_subset_1(k1_funct_1('#skF_4', C_513), k1_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_513, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_2782])).
% 5.74/2.11  tff(c_2786, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2785])).
% 5.74/2.11  tff(c_2798, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2786, c_2])).
% 5.74/2.11  tff(c_2801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_2798])).
% 5.74/2.11  tff(c_2804, plain, (![C_516]: (m1_subset_1(k1_funct_1('#skF_4', C_516), k1_relat_1('#skF_5')) | ~r2_hidden(C_516, '#skF_2'))), inference(splitRight, [status(thm)], [c_2785])).
% 5.74/2.11  tff(c_95, plain, (![C_70, B_71, A_72]: (~v1_xboole_0(C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.74/2.11  tff(c_132, plain, (![B_79, A_80, A_81]: (~v1_xboole_0(B_79) | ~r2_hidden(A_80, A_81) | ~r1_tarski(A_81, B_79))), inference(resolution, [status(thm)], [c_10, c_95])).
% 5.74/2.11  tff(c_200, plain, (![B_99, B_100, A_101]: (~v1_xboole_0(B_99) | ~r1_tarski(B_100, B_99) | v1_xboole_0(B_100) | ~m1_subset_1(A_101, B_100))), inference(resolution, [status(thm)], [c_6, c_132])).
% 5.74/2.11  tff(c_207, plain, (![A_101]: (~v1_xboole_0(k1_relat_1('#skF_5')) | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(A_101, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_195, c_200])).
% 5.74/2.11  tff(c_2400, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_207])).
% 5.74/2.11  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_70])).
% 5.74/2.11  tff(c_120, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_107])).
% 5.74/2.11  tff(c_2732, plain, (![A_502]: (k7_partfun1('#skF_1', '#skF_5', A_502)=k1_funct_1('#skF_5', A_502) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_502, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_120, c_2730])).
% 5.74/2.11  tff(c_2737, plain, (![A_502]: (k7_partfun1('#skF_1', '#skF_5', A_502)=k1_funct_1('#skF_5', A_502) | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_502, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_40, c_2732])).
% 5.74/2.11  tff(c_2738, plain, (![A_502]: (k7_partfun1('#skF_1', '#skF_5', A_502)=k1_funct_1('#skF_5', A_502) | ~m1_subset_1(A_502, k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2400, c_2737])).
% 5.74/2.11  tff(c_2820, plain, (![C_517]: (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', C_517))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_517)) | ~r2_hidden(C_517, '#skF_2'))), inference(resolution, [status(thm)], [c_2804, c_2738])).
% 5.74/2.11  tff(c_30, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.74/2.11  tff(c_2826, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2820, c_30])).
% 5.74/2.11  tff(c_2832, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(splitLeft, [status(thm)], [c_2826])).
% 5.74/2.11  tff(c_2835, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_2832])).
% 5.74/2.11  tff(c_2838, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2835])).
% 5.74/2.11  tff(c_2840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2819, c_2838])).
% 5.74/2.11  tff(c_2841, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_2826])).
% 5.74/2.11  tff(c_2858, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2716, c_2841])).
% 5.74/2.11  tff(c_2862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2858])).
% 5.74/2.11  tff(c_2864, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_207])).
% 5.74/2.11  tff(c_2868, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2864, c_4])).
% 5.74/2.11  tff(c_2870, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2868, c_195])).
% 5.74/2.11  tff(c_102, plain, (![B_5, A_72, A_4]: (~v1_xboole_0(B_5) | ~r2_hidden(A_72, A_4) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_10, c_95])).
% 5.74/2.11  tff(c_2958, plain, (![B_537, C_536, A_535, D_534, B_538]: (~v1_xboole_0(B_537) | ~r1_tarski(k2_relset_1(A_535, B_538, D_534), B_537) | k1_xboole_0=B_538 | ~r2_hidden(C_536, A_535) | ~m1_subset_1(D_534, k1_zfmisc_1(k2_zfmisc_1(A_535, B_538))) | ~v1_funct_2(D_534, A_535, B_538) | ~v1_funct_1(D_534))), inference(resolution, [status(thm)], [c_1664, c_102])).
% 5.74/2.11  tff(c_2960, plain, (![C_536]: (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_3' | ~r2_hidden(C_536, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2870, c_2958])).
% 5.74/2.11  tff(c_2963, plain, (![C_536]: (k1_xboole_0='#skF_3' | ~r2_hidden(C_536, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_2, c_2960])).
% 5.74/2.11  tff(c_2965, plain, (![C_539]: (~r2_hidden(C_539, '#skF_2'))), inference(splitLeft, [status(thm)], [c_2963])).
% 5.74/2.11  tff(c_2970, plain, (![A_2]: (v1_xboole_0('#skF_2') | ~m1_subset_1(A_2, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_2965])).
% 5.74/2.11  tff(c_2971, plain, (![A_2]: (~m1_subset_1(A_2, '#skF_2'))), inference(splitLeft, [status(thm)], [c_2970])).
% 5.74/2.11  tff(c_2985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2971, c_36])).
% 5.74/2.11  tff(c_2986, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_2970])).
% 5.74/2.11  tff(c_2989, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2986, c_4])).
% 5.74/2.11  tff(c_2993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_2989])).
% 5.74/2.11  tff(c_2994, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2963])).
% 5.74/2.11  tff(c_3007, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_2])).
% 5.74/2.11  tff(c_3010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_3007])).
% 5.74/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.11  
% 5.74/2.11  Inference rules
% 5.74/2.11  ----------------------
% 5.74/2.11  #Ref     : 0
% 5.74/2.11  #Sup     : 533
% 5.74/2.11  #Fact    : 0
% 5.74/2.11  #Define  : 0
% 5.74/2.11  #Split   : 76
% 5.74/2.11  #Chain   : 0
% 5.74/2.11  #Close   : 0
% 5.74/2.11  
% 5.74/2.11  Ordering : KBO
% 5.74/2.11  
% 5.74/2.11  Simplification rules
% 5.74/2.11  ----------------------
% 5.74/2.11  #Subsume      : 89
% 5.74/2.11  #Demod        : 762
% 5.74/2.11  #Tautology    : 190
% 5.74/2.11  #SimpNegUnit  : 89
% 5.74/2.11  #BackRed      : 288
% 5.74/2.11  
% 5.74/2.11  #Partial instantiations: 0
% 5.74/2.11  #Strategies tried      : 1
% 5.74/2.11  
% 5.74/2.11  Timing (in seconds)
% 5.74/2.11  ----------------------
% 5.74/2.11  Preprocessing        : 0.36
% 5.74/2.11  Parsing              : 0.19
% 5.74/2.11  CNF conversion       : 0.03
% 5.74/2.11  Main loop            : 0.99
% 5.74/2.11  Inferencing          : 0.34
% 5.74/2.11  Reduction            : 0.34
% 5.74/2.11  Demodulation         : 0.23
% 5.74/2.11  BG Simplification    : 0.04
% 5.74/2.11  Subsumption          : 0.20
% 5.74/2.11  Abstraction          : 0.05
% 5.74/2.11  MUC search           : 0.00
% 5.74/2.11  Cooper               : 0.00
% 5.74/2.11  Total                : 1.40
% 5.74/2.11  Index Insertion      : 0.00
% 5.74/2.11  Index Deletion       : 0.00
% 5.74/2.11  Index Matching       : 0.00
% 5.74/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
