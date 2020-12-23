%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1084+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:23 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 188 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :  186 ( 526 expanded)
%              Number of equality atoms :   24 (  64 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_77,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r2_funct_2(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(c_28,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    ! [A_22] : k6_relat_1(A_22) = k6_partfun1(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    ! [A_17] : v1_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    ! [A_17] : v1_funct_1(k6_partfun1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18])).

tff(c_12,plain,(
    ! [A_16] : v1_partfun1(k6_partfun1(A_16),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_16] : m1_subset_1(k6_partfun1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_funct_2(C_42,A_43,B_44)
      | ~ v1_partfun1(C_42,A_43)
      | ~ v1_funct_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_69,plain,(
    ! [A_16] :
      ( v1_funct_2(k6_partfun1(A_16),A_16,A_16)
      | ~ v1_partfun1(k6_partfun1(A_16),A_16)
      | ~ v1_funct_1(k6_partfun1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_75,plain,(
    ! [A_16] : v1_funct_2(k6_partfun1(A_16),A_16,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12,c_69])).

tff(c_88,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( m1_subset_1('#skF_1'(A_50,B_51,C_52,D_53),A_50)
      | r2_funct_2(A_50,B_51,C_52,D_53)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_2(D_53,A_50,B_51)
      | ~ v1_funct_1(D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_2(C_52,A_50,B_51)
      | ~ v1_funct_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    ! [A_16,C_52] :
      ( m1_subset_1('#skF_1'(A_16,A_16,C_52,k6_partfun1(A_16)),A_16)
      | r2_funct_2(A_16,A_16,C_52,k6_partfun1(A_16))
      | ~ v1_funct_2(k6_partfun1(A_16),A_16,A_16)
      | ~ v1_funct_1(k6_partfun1(A_16))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_16,A_16)))
      | ~ v1_funct_2(C_52,A_16,A_16)
      | ~ v1_funct_1(C_52) ) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_95,plain,(
    ! [A_16,C_52] :
      ( m1_subset_1('#skF_1'(A_16,A_16,C_52,k6_partfun1(A_16)),A_16)
      | r2_funct_2(A_16,A_16,C_52,k6_partfun1(A_16))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_16,A_16)))
      | ~ v1_funct_2(C_52,A_16,A_16)
      | ~ v1_funct_1(C_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_75,c_90])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,B_24)
      | v1_xboole_0(B_24)
      | ~ m1_subset_1(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_115,plain,(
    ! [A_55,C_56] :
      ( m1_subset_1('#skF_1'(A_55,A_55,C_56,k6_partfun1(A_55)),A_55)
      | r2_funct_2(A_55,A_55,C_56,k6_partfun1(A_55))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_55,A_55)))
      | ~ v1_funct_2(C_56,A_55,A_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_75,c_90])).

tff(c_30,plain,(
    ! [C_31] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_31) = C_31
      | ~ m1_subset_1(C_31,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_148,plain,(
    ! [C_62] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_2',C_62,k6_partfun1('#skF_2'))) = '#skF_1'('#skF_2','#skF_2',C_62,k6_partfun1('#skF_2'))
      | r2_funct_2('#skF_2','#skF_2',C_62,k6_partfun1('#skF_2'))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_62,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_62) ) ),
    inference(resolution,[status(thm)],[c_115,c_30])).

tff(c_159,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))) = '#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))
    | r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_148])).

tff(c_166,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))) = '#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))
    | r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_159])).

tff(c_167,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))) = '#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_166])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k3_funct_2(A_18,B_19,C_20,D_21) = k1_funct_1(C_20,D_21)
      | ~ m1_subset_1(D_21,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_244,plain,(
    ! [A_86,B_87,C_88,C_89] :
      ( k3_funct_2(A_86,B_87,C_88,'#skF_1'(A_86,A_86,C_89,k6_partfun1(A_86))) = k1_funct_1(C_88,'#skF_1'(A_86,A_86,C_89,k6_partfun1(A_86)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_2(C_88,A_86,B_87)
      | ~ v1_funct_1(C_88)
      | v1_xboole_0(A_86)
      | r2_funct_2(A_86,A_86,C_89,k6_partfun1(A_86))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_86,A_86)))
      | ~ v1_funct_2(C_89,A_86,A_86)
      | ~ v1_funct_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_115,c_20])).

tff(c_251,plain,(
    ! [C_89] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_2',C_89,k6_partfun1('#skF_2'))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2',C_89,k6_partfun1('#skF_2')))
      | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | v1_xboole_0('#skF_2')
      | r2_funct_2('#skF_2','#skF_2',C_89,k6_partfun1('#skF_2'))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_89,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_32,c_244])).

tff(c_258,plain,(
    ! [C_89] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_2',C_89,k6_partfun1('#skF_2'))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2',C_89,k6_partfun1('#skF_2')))
      | v1_xboole_0('#skF_2')
      | r2_funct_2('#skF_2','#skF_2',C_89,k6_partfun1('#skF_2'))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_89,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_251])).

tff(c_260,plain,(
    ! [C_90] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_2',C_90,k6_partfun1('#skF_2'))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2',C_90,k6_partfun1('#skF_2')))
      | r2_funct_2('#skF_2','#skF_2',C_90,k6_partfun1('#skF_2'))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_90,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_258])).

tff(c_271,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')))
    | r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_260])).

tff(c_278,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))) = '#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))
    | r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_167,c_271])).

tff(c_279,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))) = '#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_278])).

tff(c_26,plain,(
    ! [B_26,A_25] :
      ( k1_funct_1(k6_relat_1(B_26),A_25) = A_25
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_39,plain,(
    ! [B_26,A_25] :
      ( k1_funct_1(k6_partfun1(B_26),A_25) = A_25
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_197,plain,(
    ! [D_70,A_71,B_72,C_73] :
      ( k1_funct_1(D_70,'#skF_1'(A_71,B_72,C_73,D_70)) != k1_funct_1(C_73,'#skF_1'(A_71,B_72,C_73,D_70))
      | r2_funct_2(A_71,B_72,C_73,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(D_70,A_71,B_72)
      | ~ v1_funct_1(D_70)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_73,A_71,B_72)
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_200,plain,(
    ! [C_73,A_71,B_72,B_26] :
      ( k1_funct_1(C_73,'#skF_1'(A_71,B_72,C_73,k6_partfun1(B_26))) != '#skF_1'(A_71,B_72,C_73,k6_partfun1(B_26))
      | r2_funct_2(A_71,B_72,C_73,k6_partfun1(B_26))
      | ~ m1_subset_1(k6_partfun1(B_26),k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(k6_partfun1(B_26),A_71,B_72)
      | ~ v1_funct_1(k6_partfun1(B_26))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_73,A_71,B_72)
      | ~ v1_funct_1(C_73)
      | ~ r2_hidden('#skF_1'(A_71,B_72,C_73,k6_partfun1(B_26)),B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_197])).

tff(c_298,plain,(
    ! [C_97,A_98,B_99,B_100] :
      ( k1_funct_1(C_97,'#skF_1'(A_98,B_99,C_97,k6_partfun1(B_100))) != '#skF_1'(A_98,B_99,C_97,k6_partfun1(B_100))
      | r2_funct_2(A_98,B_99,C_97,k6_partfun1(B_100))
      | ~ m1_subset_1(k6_partfun1(B_100),k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ v1_funct_2(k6_partfun1(B_100),A_98,B_99)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ v1_funct_2(C_97,A_98,B_99)
      | ~ v1_funct_1(C_97)
      | ~ r2_hidden('#skF_1'(A_98,B_99,C_97,k6_partfun1(B_100)),B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_200])).

tff(c_300,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2(k6_partfun1('#skF_2'),'#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_298])).

tff(c_306,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_75,c_14,c_300])).

tff(c_307,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_306])).

tff(c_313,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_307])).

tff(c_316,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_313])).

tff(c_327,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_316])).

tff(c_330,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_327])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_330])).

%------------------------------------------------------------------------------
